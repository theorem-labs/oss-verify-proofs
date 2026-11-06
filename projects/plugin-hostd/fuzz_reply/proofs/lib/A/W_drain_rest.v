(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the REST segment of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x83a4c .. 0x83ab4): s->used = |W| - p, the move-down of the incomplete line to the buffer's start
   (__asan_memmove at 0x83a68) and the long-line reset (s->used = 0, s->skip = 1), back to the outer loop's head.
   The statement is W_drain_cx.v's dr_rest_stmt; the Section header below is that file's, verbatim. *)
(* ARx form (route (b), step 3): Section cx proves dr_rest_x, W_drain_cx_x.v's dr_rest_stmt_x at the room texts, over
   any allocator relation ARx, its journal at W_contract_x.v's DRAIN_STK_x; the AR walk dr_rest (Section c) is
   unchanged. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_rest_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
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
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
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


(* ---- The entry symbolic state at DLR (0x83a4c). ----
   Atoms: the 32 registers, then 32 = SA (the relay entry), 33 = s->skip at entry, 34 = shadow (SA + 32),
   35 = shadow SA.  The shadow base is s5's own atom (Bx = SOff 21 0), so `ld a0,192(sp); add a0,a0,s5` builds
   the form YCbn.v's match_x reads as a shadow load.  s11 = SA + 24 is pinned.  The frame region holds the eight
   slots the segment reads (no write window); the relay entry gets two write windows, s->skip [8, 12) and
   s->used [24, 32), and the shadow list covers its 56 bytes, so every shadow fast check folds to 0. *)
Definition RBx : sv := SOff 21 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rs_frame : YP09.region := YP09.mkRegion (Some 2%nat) 64 232 64 64
  [ YP09.mkChunk 64 (CVal 8 (SOff 32 32));
    YP09.mkChunk 160 (CVal 8 (SOff 34 0));
    YP09.mkChunk 176 (CVal 8 (SOff 35 0));
    YP09.mkChunk 184 (CVal 8 (SLit 6001));
    YP09.mkChunk 192 (CVal 8 (SAlu ALU_SRL (SOff 32 8) (SLit 3)));
    YP09.mkChunk 200 (CVal 8 (SOff 32 16));
    YP09.mkChunk 208 (CVal 8 (SOff 32 8));
    YP09.mkChunk 224 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 24) (SLit 3)) (SOff 21 0))) ].
Definition rs_skip : YP09.region := YP09.mkRegion (Some 32%nat) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition rs_used : YP09.region := YP09.mkRegion (Some 32%nat) 24 32 24 32 [].
Definition rs_regions : smem := [rs_frame; rs_skip; rs_used].
Definition rs_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (21%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 0);
            (33%nat, mkAF 0 1 0) ] [] [].
Definition rs_regs : list sv := sr_set sr_atoms 27%bv (SOff 32 24).
Definition ss_rs : sstate := mkSS A_dr_rest rs_regs rs_regions None rs_facts.
Definition rs_SH : list shent := [mkSHE 32 0 56].
Definition rs_extra (SA sk : Z) : list word := map (Z_to_bv 64) [SA; sk; shadow_addr (SA + 32); shadow_addr SA].

Lemma rs_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma rs_div8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma rs_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. pose proof (rs_div8 (v + c) Hc). lia.
Qed.

Lemma rs_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 21 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H21 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (rs_U_srl E n v c Hn Hv Hc), (U_atom E 21 SB H21) by (unfold SB; lia).
pose proof (rs_div8 (v + c) Hc) as Hd.
replace SB with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma rs_shadow_range : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (rs_div8 x ltac:(lia)). lia. Qed.

Lemma rs_entry : forall (W : world SEGS) regs mem SA sk,
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs -> spZ regs mod 16 = 0 ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
getr regs 27 = w64 (SA + 24) -> getr regs 21 = w64 SHADOW_OFF -> 0 <= sk <= 1 ->
val_mem SEGS (arm W mem) (spZ regs + 64) 8 (SA + 32) ->
val_mem SEGS (arm W mem) (spZ regs + 160) 8 (shadow_addr (SA + 32)) ->
val_mem SEGS (arm W mem) (spZ regs + 176) 8 (shadow_addr SA) ->
val_mem SEGS (arm W mem) (spZ regs + 184) 8 6001 ->
val_mem SEGS (arm W mem) (spZ regs + 192) 8 ((SA + 8) / 8) ->
val_mem SEGS (arm W mem) (spZ regs + 200) 8 (SA + 16) ->
val_mem SEGS (arm W mem) (spZ regs + 208) 8 (SA + 8) ->
val_mem SEGS (arm W mem) (spZ regs + 224) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W mem) (SA + 8) 4 sk ->
awr W mem SA AENT ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rs_extra SA sk))) ss_rs
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_rest)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SA sk Hceil Htop Hlo Hal HSA1 HSA2 R27 R21 Hsk M64 M160 M176 M184 M192 M200 M208 M224 Msk Hawr.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rs_extra SA sk))).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E21 : ew E 21 = getr regs 21)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sk)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (SA + 32)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (shadow_addr SA))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E21' : ew E 21 = Z_to_bv 64 SB) by (rewrite E21, R21; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (USA : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (rs_shadow_range (SA + 32) ltac:(lia)) as SR32.
pose proof (rs_shadow_range SA ltac:(lia)) as SR0.
pose proof (rs_shadow_range (SA + 24) ltac:(lia)) as SR24.
pose proof (rs_div8 (SA + 8) ltac:(lia)) as SD8.
unfold ss_rs, A_dr_rest. apply pa_entry_st_ok_full.
- unfold rs_regs. apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite (den_atom E 32 SA 24 E32) by lia. exact R27.
- vm_compute. reflexivity.
- unfold rs_regions, rs_frame, rs_skip, rs_used.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold DRAIN_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 64 8 (SOff 32 32) (SA + 32));
        [rewrite (den_atom E 32 SA 32 E32) by lia; reflexivity | zside | zside | exact M64].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 160 8 (SOff 34 0) (shadow_addr (SA + 32)));
        [rewrite (den_atom0 E 34 _ E34) by lia; reflexivity | zside | zside | exact M160].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 176 8 (SOff 35 0) (shadow_addr SA));
        [rewrite (den_atom0 E 35 _ E35) by lia; reflexivity | zside | zside | exact M176].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 184 8 (SLit 6001) 6001); [reflexivity | zside | zside | exact M184].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 192 8 _ ((SA + 8) / 8));
        [apply rs_den; apply (rs_U_srl E 32 SA 8 E32); lia | zside | zside | exact M192].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 200 8 (SOff 32 16) (SA + 16));
        [rewrite (den_atom E 32 SA 16 E32) by lia; reflexivity | zside | zside | exact M200].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 208 8 (SOff 32 8) (SA + 8));
        [rewrite (den_atom E 32 SA 8 E32) by lia; reflexivity | zside | zside | exact M208].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 224 8 _ (shadow_addr (SA + 24)));
        [apply rs_den; rewrite (rs_U_shadow E 32 SA 24 E32 E21') by lia; reflexivity | zside | zside | exact M224].
  + rewrite USA. split; [lia|]. split; [lia|].
    split; [intros o Ho; exact (Hawr o ltac:(unfold AENT; lia))|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ SA 8 4 (SOff 33 0) sk);
      [rewrite (den_atom0 E 33 sk E33) by lia; reflexivity | zside | zside | exact Msk].
  + rewrite USA. split; [lia|]. split; [lia|].
    split; [intros o Ho; exact (Hawr o ltac:(unfold AENT; lia))|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold rs_regions, rs_frame, rs_skip, rs_used, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, USA.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, USA, E21', E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- Byte images of the relay entry's cells (copied from this lane's W_gsbytes_scratch.v). ---- *)
Lemma rs_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma rs_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma rs_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.
Lemma rs_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rs_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, rs_nth_zle by exact Hk. rewrite rs_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma rs_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma rs_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma rs_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.
Lemma rs_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite rs_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite rs_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma rs_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite rs_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite rs_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite rs_le_byte1 by exact Hr. reflexivity.
Qed.
Lemma rs_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma rs_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac rs_len := rewrite ?length_app, ?rs_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac rs_len_in H := rewrite ?length_app, ?rs_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

(* s->skip is the third 4-byte field (RelayRep.v:21 entry_bytes) *)
Lemma rs_entry_skip : forall (W : world SEGS) m SA e, 0 <= re_skip e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 8) 4 (re_skip e).
Proof.
intros W m SA e Hs H.
unfold entry_bytes in H. rewrite !rs_bzs_app in H.
apply garr8_app in H as [_ H]. apply garr8_app in H as [_ H]. apply garr8_app in H as [H _].
rewrite (rs_le4_bytes (re_skip e) Hs) in H.
apply (rs_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hs|].
apply (rs_garr8_at _ _ _ _ H). rs_len. lia.
Qed.

(* ---- Blocks: two different live blocks are apart; a live block lies off the image. ---- *)
Lemma rs_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In YG0f.pairwise] in HP, Hx, Hy.
destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.
Lemma rs_pw_nodup : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> YG0f.pairwise zdisjoint l ->
List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Hzz. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Hzz. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.
Lemma rs_nodup_map_inj : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.
Lemma rs_blk_apart : forall ly S (W : world SEGS) mem md p n q m,
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
pose proof (rs_pw_nodup _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (rs_nodup_map_inj f _ _ _ Hnd Hp Hq E))).
destruct (rs_pw_in2 zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hp) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
Lemma rs_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
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
rewrite <- Eb. exact (NoDup_map_inv f _ (rs_pw_nodup _ Hpos Hpw)).
Qed.

(* a disjunction kept out of lia's sight (lia case-splits every disjunctive hypothesis in context) *)
Definition rs_hide (P : Prop) : Prop := P.
Lemma rs_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.
Lemma rs_blk_noimg : forall ly S (W : world SEGS) mem md q m a,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md q m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ q (ex_intro _ m (conj Hin Ha)))))).
Qed.
Lemma rs_amem_range_blk : forall ly S (W : world SEGS) mem md q m a n,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> 0 <= n -> a + n <= q + req_size m ->
amem_range a n.
Proof.
intros ly S W mem md q m a n HAR Hin H1 H2 H3.
destruct (al_blocks SEGS B LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma rs_amem_near : forall ly S (W : world SEGS) mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma rs_shadow_mono8 : forall x y, 0 <= x -> x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8.
Proof.
intros x y Hx Hxy. pose proof (shadow_mono x y Hxy) as M.
apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.
Lemma rs_hull_sub : forall (rd : Z -> option Z) p N x n,
shadow_hull_vis rd p N -> 0 <= p -> p <= x -> 0 < n -> x + n <= p + N -> shadow_hull_vis rd x n.
Proof.
intros rd p N x n H Hp Hpx Hn Hxn s Hs. apply H.
pose proof (rs_shadow_mono8 p x Hp Hpx). pose proof (rs_shadow_mono8 (x + n - 1) (p + N - 1) ltac:(lia) ltac:(lia)).
lia.
Qed.

Lemma rs_mbyte_of_aview2 : forall H (m m' : word -> option byte) a a',
aview SEGS H m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ---- What the segment moves: footprints, the entry's cells, the buffer. ---- *)
Lemma rs_abyte_trans : forall (W1 W2 W3 : world SEGS) m1 m2 m3 x,
abyte_kept W1 m1 W2 m2 x -> abyte_kept W2 m2 W3 m3 x -> abyte_kept W1 m1 W3 m3 x.
Proof. intros W1 W2 W3 m1 m2 m3 x [A1 B1] [A2 B2]. split; [rewrite A2; exact A1 | intros H; exact (B2 (B1 H))]. Qed.

Lemma rs_skipn_bzs : forall k l, skipn k (bzs l) = bzs (skipn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. apply IH. Qed.
Lemma rs_firstn_bzs : forall k l, firstn k (bzs l) = bzs (firstn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma rs_garr8_skipn : forall m a l k, garr8 SEGS m a l -> (k <= length l)%nat ->
garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.
Lemma rs_garr8_firstn : forall m a l k, garr8 SEGS m a l -> garr8 SEGS m a (firstn k l).
Proof. intros m a l k H. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [H _]. exact H. Qed.
Lemma rs_garr8_move : forall m m' a a' l, garr8 SEGS m a l ->
(forall j, (j < length l)%nat -> mbyte SEGS m' (a' + Z.of_nat j) = mbyte SEGS m (a + Z.of_nat j)) ->
garr8 SEGS m' a' l.
Proof.
intros m m' a a' l H Hm j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite (Hm j Hj).
specialize (Hv 0%nat Hk). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. exact Hv.
Qed.

Lemma rs_nz_in : forall U : list byte, nozero (bzs U) -> ~ In (Z_to_bv 8 0) U.
Proof.
intros U H Hin. unfold nozero, bzs in H. rewrite Forall_forall in H.
apply (H (bz (Z_to_bv 8 0))); [apply in_map; exact Hin | vm_compute; reflexivity].
Qed.

Lemma rs_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.
Lemma rs_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

(* every byte a list's predicate reads is its struct's 16 bytes or a byte of one of its blocks *)
Lemma rs_alist_fp_in : forall ly S (W : world SEGS) mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall x, fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists q m, In (q, m) (alist_blks l) /\ q <= x < q + m.
Proof.
intros ly S W mem LA l lines HL r Hr x Hx.
pose proof HL as (_ & _ & _ & _ & Hnc & Hv & _ & _ & _).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Hx; exact Hx|].
right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []].
  unfold gfp in Hx. cbn [fst snd] in Hx.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l), (AREC * hl_cap l). split.
  + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
  + unfold bzs in Hx. rewrite length_map, length_app, rs_recs_len in Hx. unfold hl_n, AREC in *.
    clear - Hx Hj Hnc. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Hx. cbn [fst snd] in Hx.
  exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. exact (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ _ Hq).
  + unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma rs_asrc_fp_in : forall ly S (W : world SEGS) mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall x, fst r <= x < snd r ->
(HA <= x < HA + 96) \/ exists q m, In (q, m) (asrc_blks h) /\ q <= x < q + m.
Proof.
intros ly S W mem HA h HS r Hr x Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. unfold ASRC in Hx. lia.
- right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx. rewrite length_map in Hx. lia.
- apply in_app_or in Hr as [Hr | Hr].
  + destruct (rs_alist_fp_in _ _ _ _ _ _ _ Hpend r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
    exists q, m. split; [right; apply in_or_app; left; exact Hq | exact Hqx].
  + apply in_app_or in Hr as [Hr | Hr].
    * destruct (rs_alist_fp_in _ _ _ _ _ _ _ Hexp r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx].
    * destruct (rs_alist_fp_in _ _ _ _ _ _ _ Hheld r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hq | exact Hqx].
Qed.

Local Ltac w_infp := repeat (first [left; reflexivity | right]).
Lemma rs_aout_fp_in : forall cap out r, In r (aout_fp B RG cap out) -> forall x, fst r <= x < snd r ->
(0x10000 <= x < 0x5fb000) \/ exists q m, In (q, m) (aout_blks cap out) /\ q <= x < q + m.
Proof.
intros cap out r Hr x Hx.
assert (GD : forall b l, In (b, l) (G_DR B RG) -> b <= x < b + l -> 0x10000 <= x < 0x5fb000).
{ intros b l Hb Hbx. apply pa_img_range. apply (proj1 (HG x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (GO : forall b l, In (b, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  b <= x < b + l -> 0x10000 <= x < 0x5fb000).
{ intros b l Hb Hbx. apply pa_img_range. apply (proj1 (HGO x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
- left. apply (GO (rg_send_max RG) 8); [w_infp | lia].
- left. apply (GD (rg_nout RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (rg_capout RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (rg_out RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GO (rg_client RG) 4); [w_infp | lia].
- left. apply (GD (rg_client_broken RG) 1); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GO (rg_send_dead RG) 1); [w_infp | lia].
- left. apply (GD (rg_send_eintr RG) 1); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (as_errno B) 4); [unfold G_DR, G_SL; w_infp | lia].
- destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  right. exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity | lia].
Qed.

(* the relay entry's 56 bytes after the two stores (s->skip, s->used), every other field kept *)
Lemma rs_entry_store : forall (W : world SEGS) m m' SA e e',
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_pad1 e' = re_pad1 e -> re_buf e' = re_buf e ->
re_cap e' = re_cap e -> re_hp e' = re_hp e -> re_keys e' = re_keys e -> re_pad2 e' = re_pad2 e ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat -> 0 <= re_skip e' < 2 ^ 32 -> 0 <= re_used e' < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m') (SA + 8) 4 (re_skip e') ->
val_mem SEGS (arm W m') (SA + 24) 8 (re_used e') ->
(forall x, SA <= x < SA + 8 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 12 <= x < SA + 24 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 32 <= x < SA + 56 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes e')).
Proof.
intros W m m' SA e e' Efd Eeof Ep1 Ebuf Ecap Ehp Ekeys Ep2 Hp1 Hp2 Hsk Hus H Vsk Vus K1 K2 K3.
assert (Enh : re_nheld e' = re_nheld e) by (unfold re_nheld; rewrite Ekeys; reflexivity).
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Ep1, Ebuf, Ecap, Ehp, Enh, Ep2.
rewrite (rs_le4_bytes (re_skip e') Hsk), (rs_le8_bytes (re_used e') Hus).
rewrite !rs_bzs_app in H |- *.
apply garr8_app in H as [H1 H]. apply garr8_app in H as [H2 H]. apply garr8_app in H as [_ H].
apply garr8_app in H as [H4 H]. apply garr8_app in H as [H5 H]. apply garr8_app in H as [_ H].
apply garr8_app in H as [H7 H]. apply garr8_app in H as [H8 H]. apply garr8_app in H as [H9 H10].
apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split;
  [|apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split;
  [|apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split]]]]]]]].
- apply (rs_garr8_kept W m W m'); [exact H1 | intros x Hx; apply K1; rs_len_in Hx; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H2); rs_len; lia | intros x Hx; apply K1; rs_len_in Hx; lia].
- apply (rs_garr8_at _ (SA + 8)); [apply rs_garr8_of_val; [change (8 * Z.of_nat 4) with 32; lia | exact Vsk] | rs_len; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H4); rs_len; lia | intros x Hx; apply K2; rs_len_in Hx; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H5); rs_len; lia | intros x Hx; apply K2; rs_len_in Hx; lia].
- apply (rs_garr8_at _ (SA + 24)); [apply rs_garr8_of_val; [change (8 * Z.of_nat 8) with 64; lia | exact Vus] | rs_len; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H7); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H8); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H9); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept W m W m'); [apply (rs_garr8_at _ _ _ _ H10); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
Qed.

(* the relay entry with new s->skip, s->used and buffer contents: the line loop's form *)
Lemma rs_okx_new : forall ly S (W : world SEGS) m m' e e',
aentry_okx B ly S W m e ->
re_eof e' = re_eof e -> re_pad1 e' = re_pad1 e -> re_pad2 e' = re_pad2 e -> re_fd e' = re_fd e ->
re_cap e' = re_cap e -> re_buf e' = re_buf e -> re_hp e' = re_hp e -> re_kh e' = re_kh e -> re_keys e' = re_keys e ->
(re_skip e' = 0 \/ re_skip e' = 1) ->
Z.of_nat (length (re_U e')) = re_used e' -> re_used e' <= re_cap e' -> 0 < re_cap e ->
Z.of_nat (length (re_junk e')) = re_cap e' - re_used e' ->
garr8 SEGS (arm W m') (re_buf e') (bzs (re_U e' ++ re_junk e')) ->
(forall q n x, In (q, n) ((if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
     map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
   q <= x < q + n -> abyte_kept W m W m' x) ->
aentry_okx B ly S W m' e'.
Proof.
intros ly S W m m' e e' (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14)
  Eeof Ep1 Ep2 Efd Ecap Ebuf Ehp Ekh Ekeys Hsk HU Huc Hcp HJ HGB KB.
assert (Enh : re_nheld e' = re_nheld e) by (unfold re_nheld; rewrite Ekeys; reflexivity).
rewrite Ecap in Huc, HJ. rewrite Ebuf in HGB.
unfold aentry_okx. rewrite Eeof, Ep1, Ep2, Efd, Ecap, Ebuf, Ehp, Ekh, Enh, Ekeys.
split; [exact K1|]. split; [exact Hsk|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
split; [exact K6|]. split; [exact HU|]. split; [exact Huc|].
split.
{ right. destruct K9 as [(C0 & _)|(Cp & BI & _)]; [lia|].
  split; [exact Cp|]. split; [exact BI|]. split; [exact HJ | exact HGB]. }
split; [exact K10|].
split.
{ destruct K11 as [Z0|(HI & HF & H8 & H8' & HBp)]; [left; exact Z0 | right].
  split; [exact HI|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
  apply (akept_garr8 W m); [|exact HBp].
  intros x Hx. apply (KB (re_hp e) (re_kh e)); [rewrite (proj2 (Z.eqb_neq _ 0) HI); left; reflexivity |].
  unfold bzs in Hx. rewrite length_map, rs_key_ptrs_len in Hx. unfold re_nheld in H8. lia. }
split; [exact K12|]. split; [exact K13|].
rewrite Forall_forall in K14 |- *. intros k Hk. destruct (K14 k Hk) as (P1 & P2 & P3 & P4).
split; [exact P1|]. split; [|split; [exact P3 | exact P4]].
apply (akept_garr8 W m); [|exact P2]. intros x Hx.
apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
- apply in_or_app. right. exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
- unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Theorem dr_rest : dr_rest_stmt B MT MMAX RG.
Proof.
intros cx s1 D p W1 c1 HB HLR Hdi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DLR in HLR.
destruct HLR as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent
  & jb & a & o & ha & ks & tl & Hc1 & Hregs & Hs8 & Hs9 & Hs10 & Hbnd & Hnonul & HDLC & Hfut).
destruct Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
unfold dr_frame in HFR. cbv zeta in HFR.
destruct HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
unfold DLC, LCORE in HDLC.
destruct HDLC as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
unfold DMEM in HMEM.
destruct HMEM as (HJ & HROM & HPRES & HFRAMES & HFR2 & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (HPRE0 & HSA0 & HGin0 & HGSA & HSAG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof HPRE0 as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & HGapp & _).
rewrite RQ in HGceil, HGapp.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
clear memS HJi.
set (SA := dxSA cx) in *.
unfold AENT, ATABLE in *.
assert (HSAb : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by lia.
assert (Hsk01 : 0 <= re_skip e1 <= 1) by (destruct HOKX as (_ & X & _); clear - X; lia).
assert (Hsp' : alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\
  spZ regs1 mod 16 = 0).
{ rewrite Hsp. unfold DRAIN_FRAME in *. repeat split; try lia. rewrite Zminus_mod, Hal16. reflexivity. }
(* ---- the relay's buffer: a live block of cap in {8192, 16384} bytes, apart from the table ---- *)
assert (HCAP : re_cap e1 = drain_b_c.ds_cap s1) by (destruct HLINK as (X & _); exact X).
assert (HUW : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & X & _); exact X).
pose proof HRST as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & K7 & K8 & K9 & _).
assert (HLW : length (dW s1) = length (re_U e1)) by (rewrite <- HUW; apply rs_bzs_len).
assert (HCAPb : 4096 <= re_cap e1) by (clear - RS_gr HCAP; unfold ulen in RS_gr; lia).
destruct K9 as [(Hc0 & _)|(Hcp & HBin & HJlen & HBUFG)]; [clear - Hc0 HCAPb; lia|].
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - HCAPb; lia); reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HBin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & _).
rewrite RQB in Hbceil, Hbapp, Hbpres.
pose proof Hbnd as (Hbp & _).
pose (NN := Z.of_nat (length (dW s1) - p)).
assert (HNN : 0 <= NN /\ Z.of_nat p + NN = re_used e1) by (unfold NN; clear - HLW K7 Hbp; lia).
assert (HTB : rs_hide (dxG cx + 896 <= re_buf e1 \/ re_buf e1 + re_cap e1 <= dxG cx)).
{ pose proof (rs_blk_apart _ _ _ _ _ _ _ _ _ HAR HGin1 HBin ltac:(intros X; injection X; clear - HCAPb; lia)) as X.
  rewrite RQ, RQB in X. exact X. }
pose proof (Permutation_NoDup HPERM (rs_ablocks_nodup _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot HNDp].
(* ---- FIN: the loop's top in the round state dnext s1, from the memory after the segment (plain drain_b.v FIN
   in rest_step).  Only s->skip, s->used, the first NN bytes of the buffer and the callee's scratch below the
   frame changed; presence only grew. ---- *)
lazymatch goal with |- SRr _ _ _ ?QPOST =>
assert (FIN : forall regs4 mem4 md4 used' sk',
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mem4 md4 k1 ->
  dregs_top RG cx regs4 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
     ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mem4 x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mem4 x) ->
  val_mem SEGS (arm W1 mem4) (SA + 24) 8 used' ->
  val_mem SEGS (arm W1 mem4) (SA + 8) 4 sk' ->
  (forall i, 0 <= i < NN -> aview SEGS (w_H W1) mem4 (re_buf e1 + i) =
                            aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)) ->
  rs_hide ((NN < 6001 /\ used' = NN /\ sk' = re_skip e1) \/ (6001 <= NN /\ used' = 0 /\ sk' = 1)) ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_top) regs4 mem4 md4) QPOST) end.
{ intros regs4 mem4 md4 used' sk' HJ4 HR4 KEEP PRES VU VS VB BR4. apply Hdi.
  (* ---- the model: no line from p on; chunk keeps skipn p W or resets it ---- *)
  pose proof RS_J1 as (_ & _ & _ & NZU).
  pose proof (rm_drlq_nil s1 p Hbnd Hnonul) as DQ.
  pose proof (rm_drl s1 p NZU Hbnd Hnonul) as DRL.
  assert (LSK : Z.of_nat (length (skipn p (dW s1))) = NN) by (rewrite length_skipn; reflexivity).
  assert (LL : Z.of_nat LINE_LIMIT = 6000) by reflexivity.
  assert (CK2 : drl s1 = lines (drain_b_c.ds_ref s1) (ddata s1) /\
    J1 (fst (fst (dchunk s1))) (snd (fst (dchunk s1))) (feed (drain_b_c.ds_ref s1) (ddata s1))).
  { pose proof (chunk_ok (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) (ddata s1) RS_J1) as CK.
    unfold drl, dchunk. destruct (chunk (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as [[u'' sk''] ls].
    cbv beta iota in CK. exact CK. }
  assert (LINES : lines (dSTR cx) (D ++ ddata s1) = lines (dSTR cx) D ++ drlp s1 p).
  { rewrite lines_app, <- RS_ref, <- (proj1 CK2), DRL. reflexivity. }
  assert (EH : drain_b_c.ds_H (dnext (dlive cx) (dxmx cx) s1) = dlH cx s1 p)
    by (unfold dnext, dlH, dlrun; cbn [drain_b_c.ds_H]; rewrite DRL; reflexivity).
  assert (EKA : drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1) = dlka cx s1 p)
    by (unfold dnext, dlka, dlrun; cbn [drain_b_c.ds_ka]; rewrite DRL; reflexivity).
  assert (EOC : drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) = dloc cx s1 p)
    by (unfold dnext, dloc, dlrun; cbn [drain_b_c.ds_ocap]; rewrite DRL; reflexivity).
  assert (ENO : drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) = dlno s1 p)
    by (unfold dnext, dlno; cbn [drain_b_c.ds_no]; rewrite DRL; reflexivity).
  (* ---- what the segment kept ---- *)
  assert (HSPb' : alloc_ceiling + 16848 <= dsp0 cx) by (unfold DRAIN_FRAME in *; lia).
  assert (HSPt : dsp0 cx <= 2 ^ 47) by (rewrite Hsp in Hsp'; unfold DRAIN_FRAME in *; lia).
  assert (NNC : NN <= re_cap e1) by (clear - HNN K8; lia).
  assert (KK : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
     ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
     abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx N1 N2 N3 N4. split; [exact (KEEP x Hx N1 N2 N3 N4)|].
    intros Hw. exact (writable_kept (w_H W1) m1 mem4 x (PRES x) Hw). }
  assert (OFFG : rs_hide (dxG cx + 896 <= 0x10000 \/ 0x5fb000 <= dxG cx)).
  { pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR HGin1) as X. unfold off_img in X. rewrite RQ in X. exact X. }
  assert (OFFB : rs_hide (re_buf e1 + re_cap e1 <= 0x10000 \/ 0x5fb000 <= re_buf e1)).
  { pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR HBin) as X. unfold off_img in X. rewrite RQB in X. exact X. }
  assert (KBand : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx. unfold rs_hide in OFFG, OFFB.
    apply KK; clear - Hx OFFG OFFB HGSA HSAG NNC HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia. }
  assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx. apply KK; clear - Hx HSPb' HSPt Hbceil NNC HSAb; unfold ESTACK, DRAIN_FRAME in *; lia. }
  lazymatch type of Hbufnot with ~ In _ ?RR0 =>
  assert (RRab : forall b, In b RR0 -> In b (ablocks B ly1 S1));
  [ intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; unfold aentry_blks;
    rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - Hcp; lia); right; exact Hb
  | assert (KB : forall q m x, In (q, m) RR0 -> q <= x < q + m -> abyte_kept W1 m1 W1 mem4 x) ] end.
  { intros q m x Hq Hx.
    pose proof (RRab _ Hq) as Hab.
    assert (Nb : (q, m) <> (re_buf e1, re_cap e1)) by (intros E; apply Hbufnot; rewrite <- E; exact Hq).
    assert (Ng : (q, m) <> (dxG cx, 896)) by (intros E; apply HGnot; right; rewrite <- E; exact Hq).
    pose proof (rs_blk_apart _ _ _ _ _ _ _ _ _ HAR Hab HBin Nb) as A1. rewrite RQB in A1.
    pose proof (rs_blk_apart _ _ _ _ _ _ _ _ _ HAR Hab HGin1 Ng) as A2. rewrite RQ in A2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hab) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hm0).
    pose proof (req_size_pos m ltac:(clear - Hm0; lia)) as (_ & Hmr).
    apply KK; clear - Hx A1 A2 Hqceil Hm0 Hmr HGSA HSAG NNC HSPb' Hq4096 C1; unfold ESTACK, DRAIN_FRAME; lia. }
  (* ---- the buffer after the move-down ---- *)
  assert (LU : length (re_U e1) = (p + Z.to_nat NN)%nat) by (unfold NN; clear - HLW Hbp K7; lia).
  assert (LUJ : length (re_U e1 ++ re_junk e1) = Z.to_nat (re_cap e1))
    by (rewrite length_app; clear - K7 HJlen K8; lia).
  assert (LB1' : length (skipn p (re_U e1)) = Z.to_nat NN) by (rewrite length_skipn; clear - LU; lia).
  set (BUFB := skipn p (re_U e1) ++ skipn (Z.to_nat NN) (re_U e1 ++ re_junk e1)).
  assert (LBUF : length BUFB = Z.to_nat (re_cap e1))
    by (unfold BUFB; rewrite length_app, LB1', length_skipn, LUJ; clear - NNC HNN; lia).
  assert (GBUF : garr8 SEGS (arm W1 mem4) (re_buf e1) (bzs BUFB)).
  { unfold BUFB. rewrite rs_bzs_app. apply garr8_app. split.
    - pose proof HBUFG as G0. rewrite rs_bzs_app in G0. apply garr8_app in G0 as [GU _].
      pose proof (rs_garr8_skipn _ _ _ p GU ltac:(rewrite rs_bzs_len; clear - LU; lia)) as GS.
      rewrite rs_skipn_bzs in GS.
      apply (rs_garr8_move _ _ _ _ _ GS). intros j Hj. rewrite rs_bzs_len, LB1' in Hj.
      unfold arm. apply rs_mbyte_of_aview2. rewrite (VB (Z.of_nat j) ltac:(clear - Hj HNN; lia)). reflexivity.
    - rewrite rs_bzs_len, LB1'.
      pose proof (rs_garr8_skipn _ _ _ (Z.to_nat NN) HBUFG ltac:(rewrite rs_bzs_len, LUJ; clear - NNC HNN; lia)) as GR.
      rewrite rs_skipn_bzs in GR.
      apply (rs_garr8_kept W1 m1 W1 mem4 _ _ GR). intros x Hx. rewrite rs_bzs_len, length_skipn, LUJ in Hx.
      unfold rs_hide in HTB.
      apply KEEP; clear - Hx HTB NNC HNN HGSA HSAG Hbceil HSPb' Hb4096 C1; unfold ESTACK, DRAIN_FRAME; lia. }
  (* ---- the two arms: s->used, s->skip and the buffer's live part ---- *)
  assert (HBR : (Z.of_nat (length (firstn (Z.to_nat used') BUFB)) = used' /\
     bzs (firstn (Z.to_nat used') BUFB) = drain_b_c.ds_u (dnext (dlive cx) (dxmx cx) s1) /\
     sk' = (if drain_b_c.ds_skip (dnext (dlive cx) (dxmx cx) s1) then 1 else 0) /\
     ~ In (Z_to_bv 8 0) (firstn (Z.to_nat used') BUFB)) /\
     0 <= used' <= 6000 /\ used' <= re_cap e1 /\ rs_hide (sk' = 0 \/ sk' = 1)).
  { unfold rs_hide in BR4 |- *. destruct BR4 as [(HA & -> & ->)|(HB' & -> & ->)].
    - assert (FA : firstn (Z.to_nat NN) BUFB = skipn p (re_U e1)).
      { unfold BUFB. rewrite firstn_app, LB1', Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
        apply firstn_all2. rewrite LB1'. lia. }
      assert (LEN : (length (skipn p (dW s1)) <= LINE_LIMIT)%nat)
        by (apply Nat2Z.inj_le; rewrite LSK, LL; clear - HA; lia).
      destruct (rm_dnext_short (dlive cx) (dxmx cx) s1 p NZU Hbnd Hnonul LEN) as [E1 E2].
      rewrite FA, E1, E2. split; [split; [|split; [|split]]|split; [|split]].
      + rewrite LB1'. clear - HNN. lia.
      + rewrite <- rs_skipn_bzs, HUW. reflexivity.
      + exact (proj1 (proj2 (proj2 HLINK))).
      + apply rs_nz_in. rewrite <- rs_skipn_bzs, HUW. exact (rm_nz_rest s1 p Hnonul).
      + clear - HA HNN. lia.
      + exact NNC.
      + destruct HOKX as (_ & X & _). exact X.
    - assert (LEN : (LINE_LIMIT < length (skipn p (dW s1)))%nat)
        by (apply Nat2Z.inj_lt; rewrite LSK, LL; clear - HB'; lia).
      destruct (rm_dnext_long (dlive cx) (dxmx cx) s1 p NZU Hbnd Hnonul LEN) as [E1 E2].
      rewrite E1, E2. cbn [Z.to_nat firstn length bzs map]. split; [split; [|split; [|split]]|split; [|split]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + intros [].
      + lia.
      + clear - Hcp. lia.
      + right. reflexivity. }
  destruct HBR as ((FUL & FU & FSK & FNZ) & FUB & FUC & FSK01).
  assert (FJL : Z.of_nat (length (skipn (Z.to_nat used') BUFB)) = re_cap e1 - used')
    by (rewrite length_skipn, LBUF; clear - FUB FUC; lia).
  (* ---- the relay entry after the segment, and the rounds still to come ---- *)
  set (e' := RE (re_fd e1) (re_eof e1) sk' (re_pad1 e1) (re_buf e1) used' (re_cap e1) (re_hp e1) (re_kh e1)
    (re_pad2 e1) (re_keys e1) (firstn (Z.to_nat used') BUFB) (skipn (Z.to_nat used') BUFB)).
  pose proof Hfut as Hfut'. rewrite DQ in Hfut'. unfold dlfut in Hfut'. cbn [drain_b_c.lines_run fst snd] in Hfut'.
  destruct Hfut' as (tl2 & Hlat & Htl). cbn [app] in Htl. subst tl.
  unfold DI.
  lazymatch type of Hlat with dlater _ _ ?jb' ?a' _ =>
  exists regs4, ly1, S1, mem4, md4, k1, e', h1, out1, ev1, LB1, spent, jb', a', tl2 end.
  split; [reflexivity|]. split; [exact HR4|].
  split.
  { unfold DMEM.
    split; [exact HJ4|].
    split.
    { intros x Hx. pose proof (pa_img_range _ (rs_rom_img x Hx)) as Hb.
      rewrite (proj1 (KBand x Hb)). exact (HROM x Hx). }
    split.
    { intros x H1 H2 H3 Hp. apply PRES. exact (HPRES x H1 H2 H3 Hp). }
    split; [exact HFRAMES|].
    split.
    { assert (VMF : forall a0 n v, dsp0 cx - DRAIN_FRAME <= a0 -> a0 + Z.of_nat n <= dsp0 cx ->
        val_mem SEGS (arm W1 m1) a0 n v -> val_mem SEGS (arm W1 mem4) a0 n v).
      { intros a0 n v H1 H2 Hv. apply (akept_vm W1 m1 W1 mem4 a0 n v); [|exact Hv].
        intros y Hy. apply KFR. clear - H1 H2 Hy. lia. }
      unfold dr_frame. cbv zeta. change (dxSA cx) with SA.
      repeat (split; [apply VMF; [unfold DRAIN_FRAME; lia | unfold DRAIN_FRAME; lia | assumption]|]).
      intros i Hi. apply VMF; [unfold DRAIN_FRAME; lia | unfold DRAIN_FRAME; clear - Hi; lia | exact (Hsaved i Hi)]. }
    split.
    { apply (rs_entry_store W1 m1 mem4 SA e1 e'); try reflexivity.
      - destruct HOKX as (_ & _ & X & _). exact X.
      - destruct HOKX as (_ & _ & _ & X & _). exact X.
      - change (0 <= sk' < 2 ^ 32). unfold rs_hide in FSK01. clear - FSK01. lia.
      - change (0 <= used' < 2 ^ 64). clear - FUB. lia.
      - exact HENT.
      - exact VS.
      - exact VU.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia. }
    split.
    { intros i Hi. apply (writable_kept (w_H W1) m1 mem4 _ (PRES _)). exact (HAWR i Hi). }
    split.
    { apply (rs_okx_new ly1 S1 W1 m1 mem4 e1 e' HOKX); try reflexivity.
      - unfold rs_hide in FSK01. exact FSK01.
      - exact FUL.
      - exact FUC.
      - exact Hcp.
      - exact FJL.
      - change (garr8 SEGS (arm W1 mem4) (re_buf e1)
          (bzs (firstn (Z.to_nat used') BUFB ++ skipn (Z.to_nat used') BUFB))).
        rewrite firstn_skipn. exact GBUF.
      - intros q n x Hq Hx. apply (KB q n x); [apply in_or_app; left; exact Hq | exact Hx]. }
    split.
    { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _).
      eapply asrc_at_kept; [exact HSRC | |
        intros b Hb; apply RRab; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (rs_asrc_fp_in _ _ _ _ _ _ HSRC r Hr x Hx) as [Hg | (q & m & Hq & Hqx)].
      - apply KBand. pose proof HGSB as (G1 & G2 & _). unfold dHA, ASRC in *. clear - Hg Hj4 G1 G2. lia.
      - apply (KB q m x); [apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx]. }
    split.
    { intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & V1 & V2 & Ho). exists f, o'.
      pose proof HGSB as (G1 & G2 & _). unfold ASRC in *.
      split; [|split; [|exact Ho]];
        (apply (akept_vm W1 m1); [intros y Hy; apply KBand; clear - Hy Hi G1 G2; lia | assumption]). }
    split.
    { intros x Hx Hn. apply (rs_abyte_trans _ _ _ _ _ _ x (HKEPT x Hx Hn)).
      apply KBand. pose proof HGSB as (G1 & G2 & _). unfold ASRC in *. clear - Hx G1 G2. lia. }
    split.
    { rewrite LINES, ENO, EOC.
      eapply aout_at_kept; [exact HOUT | |
        intros b Hb; apply RRab; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (rs_aout_fp_in _ _ r Hr x Hx) as [Hb | (q & m & Hq & Hqx)].
      - exact (KBand x Hb).
      - apply (KB q m x); [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx]. }
    split.
    { intros Hl. rewrite EOC. exact (HLIVE Hl). }
    rewrite EOC. exact HPERM. }
  split; [exact FNZ|]. split; [change (used' <= APARTIAL); unfold APARTIAL; clear - FUB; lia|].
  split.
  { unfold DLINK. pose proof HLINK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
    destruct (dneed_dnext (dlive cx) (dxmx cx) s1 RS_gr RS_pe RS_wf RS_st RS_ei) as [_ WFn].
    split; [exact HCAP|]. split; [exact FU|]. split; [exact FSK|].
    split; [rewrite EH; exact L4|]. split; [rewrite EKA; exact L5|].
    split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|].
    split; [exact L10|]. split; [exact L11 | exact WFn]. }
  split; [exact HSAME|].
  split.
  { rewrite LINES. pose proof HHIST as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    unfold DHIST. rewrite EH, ENO. rewrite DQ in H10. cbn [length Z.of_nat] in H10.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
    split; [exact H10 | exact H11]. }
  split; [exact (proj2 CK2)|].
  split; [exact Hlat | exact HBUD]. }
pose proof (rs_entry W1 regs1 m1 SA (re_skip e1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  R27 R21 ltac:(lia) ltac:(rewrite Hsp; exact M64) ltac:(rewrite Hsp; exact F160) ltac:(rewrite Hsp; exact F176)
  ltac:(rewrite Hsp; exact F184) ltac:(rewrite Hsp; exact M192) ltac:(rewrite Hsp; exact M200)
  ltac:(rewrite Hsp; exact F208) ltac:(rewrite Hsp; exact F224)
  ltac:(apply rs_entry_skip; [lia | exact HENT]) HAWR) as HS.
subst c1. unfold cfg_at.
remember (Eimg (Ereg regs1 (rs_extra SA (re_skip e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_skip e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (SA + 32)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (shadow_addr SA))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (USA : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS RBx rs_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) m1 E RBx 32%nat SA 56 SA 0 56).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) 896); [exact HAR | exact HGin1 | lia |].
    rewrite RQ. lia.
  - unfold RBx. apply (U_atom E 21 SHADOW_OFF); [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | unfold SHADOW_OFF; lia].
  - apply (U_atom E 32 SA E32). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. unfold AENT in *. lia. }
paj_run_tok RUN HS HJ SHOK RBspan.
{ cbn [ss_mem ss_rs rs_regions].
  apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  all: (intros x Hx; cbn [rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USA in Hx;
    left; (split; [|lia]); right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
    | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
rename ms into msT.
lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGT end.
rename HF into HFT, HFr into HFrT.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
(* what the first run kept: everything but s->skip and s->used *)
assert (KT : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msT) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. apply (aview_kept_out E (ss_mem ss_rs) (w_H W1) m1 (ms_mem msT) HFrT x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_rs rs_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [rs_frame rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?USA in Hr; lia. }
assert (HART : AR SEGS B ly1 S1 W1 (ms_mem msT) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR; exact HJ).
assert (Gbuf : forall x, re_buf e1 <= x < re_buf e1 + re_cap e1 -> ~ in_img SEGS x)
  by (intros x Hx; apply (rs_blk_noimg _ _ _ _ _ _ _ x HAR HBin); rewrite RQB; lia).
assert (Gtab : forall x, dxG cx <= x < dxG cx + 896 -> ~ in_img SEGS x)
  by (intros x Hx; apply (rs_blk_noimg _ _ _ _ _ _ _ x HAR HGin1); rewrite RQ; lia).
assert (HROMT : rom_view SEGS W1 (ms_mem msT)).
{ intros x Hx. pose proof (rs_rom_img x Hx) as Hi. pose proof (Hsegs x Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite KT; [exact (HROM x Hx) | lia | intros Hw; apply (Gtab x); [lia | exact Hi] | intros Hw; apply (Gtab x); [lia | exact Hi]]. }
assert (HSPb : alloc_ceiling + 16848 <= dsp0 cx) by (unfold DRAIN_FRAME in *; lia).
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memmove)
    (fun x => re_buf e1 <= x < re_buf e1 + NN)
    (fun regs' mem' => getr regs' 10 = w64 (re_buf e1) /\
       forall i, 0 <= i < NN -> aview SEGS (w_H W1) mem' (re_buf e1 + i) =
                                aview SEGS (w_H W1) (ms_mem msT) (re_buf e1 + Z.of_nat p + i))
    W1 (ms_regs msT) (ms_mem msT) DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ).
  - unfold spZ at 1. rewrite Q2, Usp, Hsp. lia.
  - unfold DRAIN_FRAME. reflexivity.
  - unfold DRAIN_FRAME. lia.
  - lia.
  - rewrite HDS. unfold ESTACK, DRAIN_FRAME. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp0.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros x. destruct (Z_le_gt_dec (re_buf e1) x); destruct (Z_lt_ge_dec x (re_buf e1 + NN));
      [left; lia | right; lia | right; lia | right; lia].
  - intros x Hx Hg. exfalso. apply (Gbuf x); [lia | exact (proj1 (HG x Hg))].
  - intros x Hx Hng. split; [|lia].
    assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
    destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
    + right. left. split.
      * apply (Permutation_in _ HPERM0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
          [injection X as X1 X2; clear - X2 HCAPb; lia|].
        assert (Hin3 : In (re_buf e1, re_cap e1) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
        { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
          apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
          apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
          exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
          exact Hin0. }
        unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
        split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
        cbn [fst snd]. rewrite RQB. lia.
      * exists (re_buf e1), (re_cap e1). split; [exact HBin | rewrite RQB; lia].
    + right. right. left. exists (re_buf e1), (re_cap e1). split; [exact HBin|]. split; [exact Hnot0 | rewrite RQB; lia].
  - intros HPRE HSC.
    apply (AMEMMOVE ly1 S1 W1 (ms_regs msT) (ms_mem msT) _ (re_buf e1) (re_buf e1 + Z.of_nat p) NN HPRE).
    + rewrite Q10, (EE 26%nat 26%bv eq_refl). exact Hs10.
    + rewrite Q11, (EE 24%nat 24%bv eq_refl). exact Hs8.
    + rewrite Q12, (EE 25%nat 25%bv eq_refl). exact Hs9.
    + split; [lia|]. assert (HCAPu : re_cap e1 <= 16384)
        by (destruct HOKX as (_ & _ & _ & _ & _ & X & _); clear - X; lia). lia.
    + lia.
    + lia.
    + intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HART HBin) as (_ & _ & _ & _ & HP & _).
      rewrite RQB in HP. destruct (HP x ltac:(lia)) as [HPx HPo].
      split; [exact (apresent_writable SEGS _ _ _ HPx)|]. split; [exact HPo|].
      unfold spZ. rewrite Q2, Usp, Hsp. unfold ESTACK, DRAIN_FRAME. lia.
    + apply (rs_amem_range_blk _ _ _ _ _ _ _ _ _ HART HBin); [lia | lia | rewrite RQB; lia].
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros Hn. destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HART HBin) as [_ Hh]. rewrite RQB in Hh.
      apply (rs_hull_sub _ _ _ _ _ Hh); [lia | lia | exact Hn | lia].
    + lia.
    + lia.
    + intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HART HBin) as (_ & _ & _ & _ & HP & _).
      rewrite RQB in HP. destruct (HP x ltac:(lia)) as [HPx _].
      split; [exact (aview_some_of_apresent SEGS _ _ _ HPx)|].
      unfold spZ. rewrite Q2, Usp, Hsp. unfold ESTACK, DRAIN_FRAME. lia.
    + apply (rs_amem_range_blk _ _ _ _ _ _ _ _ _ HART HBin); [lia | lia | rewrite RQB; lia].
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros Hn. destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HART HBin) as [_ Hh]. rewrite RQB in Hh.
      apply (rs_hull_sub _ _ _ _ _ Hh); [lia | lia | exact Hn | lia].
    + exact HROMT.
    + intros Hn. split.
      * apply (rs_amem_near _ _ _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
      * apply (rs_amem_near _ _ _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros x Hx Hr. apply (Gbuf x); [lia | exact Hr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HR10 & HMV) & Hfr2 & Hpres2).
assert (TBX : forall x, dxG cx <= x < dxG cx + 896 -> ~ (re_buf e1 <= x < re_buf e1 + NN))
  by (intros x Hx Hb; unfold rs_hide in HTB; clear - Hx Hb HTB HNN K8; lia).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (RK : forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e1 <= x < re_buf e1 + NN) ->
    ~ (dsp0 cx + - DRAIN_FRAME - ESTACK <= x < dsp0 cx + - DRAIN_FRAME) ->
    mbyte SEGS (mrestrict (w_H W1) mem2) x = mbyte SEGS (mrestrict (w_H W1) (ms_mem msT)) x).
  { intros x Hx N1 N2. apply (mbyte_of_aview SEGS). exact (Hfr2 x Hx N1 N2). }
  assert (WK : forall x, writable_at SEGS (mrestrict (w_H W1) (ms_mem msT)) x ->
    writable_at SEGS (mrestrict (w_H W1) mem2) x)
    by (intros x Hw; exact (writable_kept (w_H W1) (ms_mem msT) mem2 x (fun Hp => Hpres2 _ Hp) Hw)).
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [rs_frame rs_skip rs_used YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?Usp, ?USA; unfold ESTACK, DRAIN_FRAME in *.
  - intros x Hx. apply RK; lia.
  - intros x Hx. lia.
  - intros x Hx. apply RK; [lia | apply TBX; lia | lia].
  - intros x _ Hw. exact (WK x Hw).
  - intros x Hx. apply RK; [lia | apply TBX; lia | lia].
  - intros x _ Hw. exact (WK x Hw). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs1) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp).
assert (USAa : bv_unsigned (ew Ea 32) = SA) by (rewrite (OLDa 32%nat ltac:(lia)); exact USA).
assert (HAR2 : AR SEGS B ly1 S1 W1 mem2 md2) by (eapply ajournal_gx_AR; exact HJ2).
assert (SHOK2 : sh_ok SEGS RBx rs_SH Ea (mrestrict (w_H W1) mem2)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea RBx 32%nat SA 56 SA 0 56).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem2 md2 (dxG cx) 896); [exact HAR2 | exact HGin1 | lia |].
    rewrite RQ. lia.
  - unfold RBx. apply (U_atom Ea 21 SHADOW_OFF);
      [rewrite (OLDa 21%nat ltac:(lia)), (EE 21%nat 21%bv eq_refl), R21; reflexivity | unfold SHADOW_OFF; lia].
  - apply (U_atom Ea 32 SA); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
paj_run_tok RUN HS HJ2 SHOK2 RBspan.
{ apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  all: (intros x Hx; cbn [rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
    left; (split; [|lia]); right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
    | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
rename ms into ms2.
lazymatch goal with H : mem_grows (mrestrict _ mem2) _ |- _ => rename H into HG2 end.
rename HF into HF2, HFr into HFr2.
assert (K2 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem ms2) x = aview SEGS (w_H W1) mem2 x).
{ intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms2) HFr2 x Hx).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
assert (E25 : ew Ea 25 = Z_to_bv 64 NN) by (rewrite (OLDa 25%nat ltac:(lia)), (EE 25%nat 25%bv eq_refl); exact Hs9).
(* the memory after the second run, against the segment's entry *)
assert (TBX' : forall x, SA <= x < SA + 56 -> ~ (re_buf e1 <= x < re_buf e1 + NN)) by (intros x Hx; apply TBX; lia).
assert (KM2 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms2) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4. rewrite (K2 x Hx N1 N2), (Hfr2 x Hx N3 ltac:(lia)). exact (KT x Hx N1 N2). }
assert (PM2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms2) x).
{ intros x Hx. apply (apresent_grows _ _ _ _ HG2). apply Hpres2. exact (apresent_grows _ _ _ _ HGT Hx). }
assert (VB2 : forall i, 0 <= i < NN -> aview SEGS (w_H W1) (ms_mem ms2) (re_buf e1 + i) =
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)).
{ intros i Hi.
  assert (NB : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> ~ (SA <= y < SA + 56)).
  { intros y Hy Hs. unfold rs_hide in HTB. clear - Hy Hs HTB HGSA HSAG. lia. }
  rewrite (K2 (re_buf e1 + i) ltac:(lia) ltac:(intros X; apply (NB (re_buf e1 + i)); lia)
    ltac:(intros X; apply (NB (re_buf e1 + i)); lia)).
  rewrite (HMV i Hi).
  exact (KT (re_buf e1 + Z.of_nat p + i) ltac:(lia) ltac:(intros X; apply (NB (re_buf e1 + Z.of_nat p + i)); lia)
    ltac:(intros X; apply (NB (re_buf e1 + Z.of_nat p + i)); lia)). }
psrr_branch_tok RUN BR HS SHOK2 RBspan.
- rewrite branch_ltu_U, (U_atom Ea 25 NN E25), (U_lit Ea 6001) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 RBspan A_dr_top.
  { apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    all: (intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
      left; (split; [|lia]); right; left; split;
      [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
      | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
  rename ms into ms3.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem ms2)) _ |- _ => rename H into HG3 end.
  rename HF into HF3, HFr into HFr3.
  assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
    aview SEGS (w_H W1) (ms_mem ms3) x = aview SEGS (w_H W1) (ms_mem ms2) x).
  { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 x Hx).
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HR4 : dregs_top RG cx (ms_regs ms3)).
  { unfold dregs_top. split; [unfold spZ; rewrite P2, Uspa; exact Hsp|].
    rewrite USAa in P25, P26, P27.
    rewrite P3, P4, P22, P25, P27, P26, P18, P9, P8, P21, P23, P24.
    rewrite (OLDa 3%nat ltac:(lia)), (OLDa 4%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)),
      (OLDa 9%nat ltac:(lia)), (OLDa 8%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)),
      (OLDa 35%nat ltac:(lia)).
    rewrite (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 18%nat 18%bv eq_refl),
      (EE 9%nat 9%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 21%nat 21%bv eq_refl), E34, E35.
    rewrite R3, R4, R22, R18, R9, R8, R21.
    repeat split; reflexivity. }
  assert (E33a : ew Ea 33 = Z_to_bv 64 (re_skip e1)) by (rewrite (OLDa 33%nat ltac:(lia)); exact E33).
  apply (FIN (ms_regs ms3) (ms_mem ms3) _ NN (re_skip e1) HJ2 HR4).
  + intros x Hx N1 N2 N3 N4. rewrite (K3 x Hx N1 N2). exact (KM2 x Hx N1 N2 N3 N4).
  + intros x Hx. exact (apresent_grows _ _ _ _ HG3 (PM2 x Hx)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 24 8%N (SOff 25 0) NN RG2 USAa (or_introl eq_refl)
      (den_atom0 Ea 25 NN E25 ltac:(lia)) ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 8 4%N (SOff 33 0) (re_skip e1) RG1 USAa (or_introl eq_refl)
      (den_atom0 Ea 33 _ E33a ltac:(lia)) ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
  + intros i Hi.
    assert (NB : ~ (SA <= re_buf e1 + i < SA + 56)) by (unfold rs_hide in HTB; clear - Hi HTB HGSA HSAG HNN K8; lia).
    rewrite (K3 (re_buf e1 + i) ltac:(lia) ltac:(lia) ltac:(lia)). exact (VB2 i Hi).
  + unfold rs_hide. left. split; [exact Hc | split; reflexivity].
- rewrite branch_ltu_U, (U_atom Ea 25 NN E25), (U_lit Ea 6001) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 RBspan A_dr_top.
  { apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    all: (intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
      left; (split; [|lia]); right; left; split;
      [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
      | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
  rename ms into ms3.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem ms2)) _ |- _ => rename H into HG3 end.
  rename HF into HF3, HFr into HFr3.
  assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
    aview SEGS (w_H W1) (ms_mem ms3) x = aview SEGS (w_H W1) (ms_mem ms2) x).
  { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 x Hx).
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HR4 : dregs_top RG cx (ms_regs ms3)).
  { unfold dregs_top. split; [unfold spZ; rewrite P2, Uspa; exact Hsp|].
    rewrite USAa in P25, P26, P27.
    rewrite P3, P4, P22, P25, P27, P26, P18, P9, P8, P21, P23, P24.
    rewrite (OLDa 3%nat ltac:(lia)), (OLDa 4%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)),
      (OLDa 9%nat ltac:(lia)), (OLDa 8%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)),
      (OLDa 35%nat ltac:(lia)).
    rewrite (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 18%nat 18%bv eq_refl),
      (EE 9%nat 9%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 21%nat 21%bv eq_refl), E34, E35.
    rewrite R3, R4, R22, R18, R9, R8, R21.
    repeat split; reflexivity. }
  apply (FIN (ms_regs ms3) (ms_mem ms3) _ 0 1 HJ2 HR4).
  + intros x Hx N1 N2 N3 N4. rewrite (K3 x Hx N1 N2). exact (KM2 x Hx N1 N2 N3 N4).
  + intros x Hx. exact (apresent_grows _ _ _ _ HG3 (PM2 x Hx)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 24 8%N (SLit 0) 0 RG2 USAa (or_introl eq_refl)
      eq_refl ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 8 4%N (SLit 1) 1 RG1 USAa (or_introl eq_refl)
      eq_refl ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
  + intros i Hi.
    assert (NB : ~ (SA <= re_buf e1 + i < SA + 56)) by (unfold rs_hide in HTB; clear - Hi HTB HGSA HSAG HNN K8; lia).
    rewrite (K3 (re_buf e1 + i) ltac:(lia) ltac:(lia) ltac:(lia)). exact (VB2 i Hi).
  + unfold rs_hide. right. split; [exact Hc | split; reflexivity].
Qed.

End c.

(* ---- THE GENERIC WALK (route (b), step 3): REST over any allocator relation ARx with its laws, at the room
   texts (the room record RP, the entry's budget kr).  The Section is W_drain_cx_x.v's Section c - its variables
   B PST ARx MT RP MMAX RG in that order, each hypothesis that file's text - with the three allocator rules in their
   caller-context forms (W_journal_x.v Section hc, one context table per allocator entry; this segment calls no
   allocator, so no call-site fact HCTX_* is stated), and after LAWS the generic-relation facts the walk reads:
     HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table's and the buffer's shadow facts are
     W_journal_x.v's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x) and BLKN (a live block's
     size is nonnegative, which cgif's al_blocks carried: the blocks' disjointness and the kept bytes read it).  An
     image byte lies in no live block (YCbqG.v blk_img_x, the laws' client-image field), which keeps the image's bytes
     across the segment without a numeric image band.
   The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are restated here with an _x
   suffix (each over ARx where it reads the relation), so no lemma's Section generalization is relied on. ---- *)
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
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
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
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 24 (W_END ++ [0]).
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

Lemma rs_den_x : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma rs_div8_x : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma rs_U_srl_x : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. pose proof (rs_div8_x (v + c) Hc). lia.
Qed.

Lemma rs_U_shadow_x : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 21 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H21 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (rs_U_srl_x E n v c Hn Hv Hc), (U_atom E 21 SB H21) by (unfold SB; lia).
pose proof (rs_div8_x (v + c) Hc) as Hd.
replace SB with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma rs_shadow_range_x : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (rs_div8_x x ltac:(lia)). lia. Qed.

Lemma rs_entry_x : forall (W : world SEGS) regs mem SA sk,
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs -> spZ regs mod 16 = 0 ->
4096 <= SA -> SA + 56 <= alloc_ceiling ->
getr regs 27 = w64 (SA + 24) -> getr regs 21 = w64 SHADOW_OFF -> 0 <= sk <= 1 ->
val_mem SEGS (arm W mem) (spZ regs + 64) 8 (SA + 32) ->
val_mem SEGS (arm W mem) (spZ regs + 160) 8 (shadow_addr (SA + 32)) ->
val_mem SEGS (arm W mem) (spZ regs + 176) 8 (shadow_addr SA) ->
val_mem SEGS (arm W mem) (spZ regs + 184) 8 6001 ->
val_mem SEGS (arm W mem) (spZ regs + 192) 8 ((SA + 8) / 8) ->
val_mem SEGS (arm W mem) (spZ regs + 200) 8 (SA + 16) ->
val_mem SEGS (arm W mem) (spZ regs + 208) 8 (SA + 8) ->
val_mem SEGS (arm W mem) (spZ regs + 224) 8 (shadow_addr (SA + 24)) ->
val_mem SEGS (arm W mem) (SA + 8) 4 sk ->
awr W mem SA AENT ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rs_extra SA sk))) ss_rs
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_rest)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SA sk Hceil Htop Hlo Hal HSA1 HSA2 R27 R21 Hsk M64 M160 M176 M184 M192 M200 M208 M224 Msk Hawr.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rs_extra SA sk))).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E21 : ew E 21 = getr regs 21)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sk)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (SA + 32)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (shadow_addr SA))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E21' : ew E 21 = Z_to_bv 64 SB) by (rewrite E21, R21; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (USA : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (rs_shadow_range_x (SA + 32) ltac:(lia)) as SR32.
pose proof (rs_shadow_range_x SA ltac:(lia)) as SR0.
pose proof (rs_shadow_range_x (SA + 24) ltac:(lia)) as SR24.
pose proof (rs_div8_x (SA + 8) ltac:(lia)) as SD8.
unfold ss_rs, A_dr_rest. apply pa_entry_st_ok_full.
- unfold rs_regs. apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite (den_atom E 32 SA 24 E32) by lia. exact R27.
- vm_compute. reflexivity.
- unfold rs_regions, rs_frame, rs_skip, rs_used.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold DRAIN_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 64 8 (SOff 32 32) (SA + 32));
        [rewrite (den_atom E 32 SA 32 E32) by lia; reflexivity | zside | zside | exact M64].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 160 8 (SOff 34 0) (shadow_addr (SA + 32)));
        [rewrite (den_atom0 E 34 _ E34) by lia; reflexivity | zside | zside | exact M160].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 176 8 (SOff 35 0) (shadow_addr SA));
        [rewrite (den_atom0 E 35 _ E35) by lia; reflexivity | zside | zside | exact M176].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 184 8 (SLit 6001) 6001); [reflexivity | zside | zside | exact M184].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 192 8 _ ((SA + 8) / 8));
        [apply rs_den_x; apply (rs_U_srl_x E 32 SA 8 E32); lia | zside | zside | exact M192].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 200 8 (SOff 32 16) (SA + 16));
        [rewrite (den_atom E 32 SA 16 E32) by lia; reflexivity | zside | zside | exact M200].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 208 8 (SOff 32 8) (SA + 8));
        [rewrite (den_atom E 32 SA 8 E32) by lia; reflexivity | zside | zside | exact M208].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 224 8 _ (shadow_addr (SA + 24)));
        [apply rs_den_x; rewrite (rs_U_shadow_x E 32 SA 24 E32 E21') by lia; reflexivity | zside | zside | exact M224].
  + rewrite USA. split; [lia|]. split; [lia|].
    split; [intros o Ho; exact (Hawr o ltac:(unfold AENT; lia))|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ SA 8 4 (SOff 33 0) sk);
      [rewrite (den_atom0 E 33 sk E33) by lia; reflexivity | zside | zside | exact Msk].
  + rewrite USA. split; [lia|]. split; [lia|].
    split; [intros o Ho; exact (Hawr o ltac:(unfold AENT; lia))|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold rs_regions, rs_frame, rs_skip, rs_used, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, USA.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, USA, E21', E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- Byte images of the relay entry's cells (copied from this lane's W_gsbytes_scratch.v). ---- *)
Lemma rs_bzs_app_x : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma rs_bzs_len_x : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma rs_bz_bv8_x : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.
Lemma rs_nth_zle_x : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rs_nth_le_bytes_x : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, rs_nth_zle_x by exact Hk. rewrite rs_bz_bv8_x.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma rs_le_byte1_x : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma rs_garr8_at_x : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma rs_garr8_kept_x : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.
Lemma rs_val_of_garr8_x : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite rs_bzs_len_x, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite rs_nth_le_bytes_x by assumption. reflexivity.
Qed.
Lemma rs_garr8_of_val_x : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite rs_bzs_len_x, length_Z_to_le_bytes in Hj; exact Hj).
rewrite rs_nth_le_bytes_x by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite rs_le_byte1_x by exact Hr. reflexivity.
Qed.
Lemma rs_le8_bytes_x : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma rs_le4_bytes_x : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac rs_len := rewrite ?length_app, ?rs_bzs_len_x, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac rs_len_in H := rewrite ?length_app, ?rs_bzs_len_x, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

(* s->skip is the third 4-byte field (RelayRep.v:21 entry_bytes) *)
Lemma rs_entry_skip_x : forall (W : world SEGS) m SA e, 0 <= re_skip e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 8) 4 (re_skip e).
Proof.
intros W m SA e Hs H.
unfold entry_bytes in H. rewrite !rs_bzs_app_x in H.
apply garr8_app in H as [_ H]. apply garr8_app in H as [_ H]. apply garr8_app in H as [H _].
rewrite (rs_le4_bytes_x (re_skip e) Hs) in H.
apply (rs_val_of_garr8_x W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hs|].
apply (rs_garr8_at_x _ _ _ _ H). rs_len. lia.
Qed.

(* ---- Blocks: two different live blocks are apart; a live block lies off the image. ---- *)
Lemma rs_pw_in2_x : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [In YG0f.pairwise] in HP, Hx, Hy.
destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- exfalso; apply Hne; reflexivity.
- left. exact (HF y Hy).
- right. exact (HF x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.
Lemma rs_pw_nodup_x : forall l : list (Z * Z), (forall x, In x l -> 1 <= snd x) -> YG0f.pairwise zdisjoint l ->
List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hpos Hpw; [apply List.NoDup_nil|].
destruct Hpw as [Hx Hl]. apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx. pose proof (Hx x Hin) as Hzz. pose proof (Hpos x (or_introl eq_refl)).
  unfold zdisjoint in Hzz. lia.
- apply IH; [intros y Hy; apply Hpos; right; exact Hy | exact Hl].
Qed.
Lemma rs_nodup_map_inj_x : forall {X Y} (f : X -> Y) (l : list X) x y,
List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z l IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. inversion Hnd as [|w ws Hz Hnd']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity | | | exact (IH x y Hnd' Hx Hy Hf)].
- exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
Qed.
Lemma rs_blk_apart_x : forall ly S Hp (W : world SEGS) mem md p n q m,
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
pose proof (rs_pw_nodup_x _ Hpos Hpw) as Hnd.
assert (Hf : f (p, n) <> f (q, m)) by (intros E; exact (Hne (rs_nodup_map_inj_x f _ _ _ Hnd Hpn Hq E))).
destruct (rs_pw_in2_x zdisjoint _ (f (p, n)) (f (q, m)) Hpw (in_map f _ _ Hpn) (in_map f _ _ Hq) Hf) as [X|X];
  unfold zdisjoint, f in X; cbn [fst snd] in X; lia.
Qed.
Lemma rs_ablocks_nodup_x : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
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
rewrite <- Eb. exact (NoDup_map_inv f _ (rs_pw_nodup_x _ Hpos Hpw)).
Qed.

Lemma rs_rom_img_x : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & H1 & _ & H3). exists sg. split; [exact H1 | exact H3]. Qed.
Lemma rs_blk_noimg_x : forall ly S Hp (W : world SEGS) mem md q m a,
ARx ly S Hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S Hp W mem md q m a HAR Hin Ha.
exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR (or_introl (ex_intro _ q (ex_intro _ m (conj Hin Ha)))))).
Qed.
Lemma rs_amem_range_blk_x : forall ly S Hp (W : world SEGS) mem md q m a n,
ARx ly S Hp W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> 0 <= n -> a + n <= q + req_size m ->
amem_range a n.
Proof.
intros ly S Hp W mem md q m a n HAR Hin H1 H2 H3.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md q m HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma rs_amem_near_x : forall ly S Hp (W : world SEGS) mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma rs_mbyte_of_aview2_x : forall H (m m' : word -> option byte) a a',
aview SEGS H m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ---- What the segment moves: footprints, the entry's cells, the buffer. ---- *)
Lemma rs_abyte_trans_x : forall (W1 W2 W3 : world SEGS) m1 m2 m3 x,
abyte_kept W1 m1 W2 m2 x -> abyte_kept W2 m2 W3 m3 x -> abyte_kept W1 m1 W3 m3 x.
Proof. intros W1 W2 W3 m1 m2 m3 x [A1 B1] [A2 B2]. split; [rewrite A2; exact A1 | intros H; exact (B2 (B1 H))]. Qed.

Lemma rs_skipn_bzs_x : forall k l, skipn k (bzs l) = bzs (skipn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. apply IH. Qed.
Lemma rs_firstn_bzs_x : forall k l, firstn k (bzs l) = bzs (firstn k l).
Proof. intros k l. unfold bzs. revert l. induction k as [|k IH]; intros [|b l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma rs_garr8_skipn_x : forall m a l k, garr8 SEGS m a l -> (k <= length l)%nat ->
garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.
Lemma rs_garr8_firstn_x : forall m a l k, garr8 SEGS m a l -> garr8 SEGS m a (firstn k l).
Proof. intros m a l k H. rewrite <- (firstn_skipn k l) in H. apply garr8_app in H as [H _]. exact H. Qed.
Lemma rs_garr8_move_x : forall m m' a a' l, garr8 SEGS m a l ->
(forall j, (j < length l)%nat -> mbyte SEGS m' (a' + Z.of_nat j) = mbyte SEGS m (a + Z.of_nat j)) ->
garr8 SEGS m' a' l.
Proof.
intros m m' a a' l H Hm j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite (Hm j Hj).
specialize (Hv 0%nat Hk). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. exact Hv.
Qed.

Lemma rs_nz_in_x : forall U : list byte, nozero (bzs U) -> ~ In (Z_to_bv 8 0) U.
Proof.
intros U H Hin. unfold nozero, bzs in H. rewrite Forall_forall in H.
apply (H (bz (Z_to_bv 8 0))); [apply in_map; exact Hin | vm_compute; reflexivity].
Qed.

Lemma rs_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.
Lemma rs_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

(* every byte a list's predicate reads is its struct's 16 bytes or a byte of one of its blocks *)
Lemma rs_alist_fp_in_x : forall ly S (W : world SEGS) mem LA l lines,
alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall x, fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists q m, In (q, m) (alist_blks l) /\ q <= x < q + m.
Proof.
intros ly S W mem LA l lines HL r Hr x Hx.
pose proof HL as (_ & _ & _ & _ & Hnc & Hv & _ & _ & _).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Hx; exact Hx|].
right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []].
  unfold gfp in Hx. cbn [fst snd] in Hx.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l), (AREC * hl_cap l). split.
  + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). left. reflexivity.
  + unfold bzs in Hx. rewrite length_map, length_app, rs_recs_len_x in Hx. unfold hl_n, AREC in *.
    clear - Hx Hj Hnc. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Hx. cbn [fst snd] in Hx.
  exists (fst q), (Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. exact (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ _ Hq).
  + unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma rs_asrc_fp_in_x : forall ly S (W : world SEGS) mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall x, fst r <= x < snd r ->
(HA <= x < HA + 96) \/ exists q m, In (q, m) (asrc_blks h) /\ q <= x < q + m.
Proof.
intros ly S W mem HA h HS r Hr x Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. unfold ASRC in Hx. lia.
- right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx. rewrite length_map in Hx. lia.
- apply in_app_or in Hr as [Hr | Hr].
  + destruct (rs_alist_fp_in_x _ _ _ _ _ _ _ Hpend r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
    exists q, m. split; [right; apply in_or_app; left; exact Hq | exact Hqx].
  + apply in_app_or in Hr as [Hr | Hr].
    * destruct (rs_alist_fp_in_x _ _ _ _ _ _ _ Hexp r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx].
    * destruct (rs_alist_fp_in_x _ _ _ _ _ _ _ Hheld r Hr x Hx) as [X | (q & m & Hq & Hqx)]; [left; lia | right].
      exists q, m. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hq | exact Hqx].
Qed.

Local Ltac w_infp := repeat (first [left; reflexivity | right]).
Lemma rs_aout_fp_in_x : forall cap out r, In r (aout_fp B RG cap out) -> forall x, fst r <= x < snd r ->
in_img SEGS x \/ exists q m, In (q, m) (aout_blks cap out) /\ q <= x < q + m.
Proof.
intros cap out r Hr x Hx.
assert (GD : forall b l, In (b, l) (G_DR B RG) -> b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HG x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
assert (GO : forall b l, In (b, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] ->
  b <= x < b + l -> in_img SEGS x).
{ intros b l Hb Hbx. apply (proj1 (HGO x ltac:(unfold inG; apply Exists_exists;
    exists (b, l); split; [exact Hb | unfold in_zr; cbn [fst snd]; lia]))). }
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
- left. apply (GO (rg_send_max RG) 8); [w_infp | lia].
- left. apply (GD (rg_nout RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (rg_capout RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (rg_out RG) 8); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GO (rg_client RG) 4); [w_infp | lia].
- left. apply (GD (rg_client_broken RG) 1); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GO (rg_send_dead RG) 1); [w_infp | lia].
- left. apply (GD (rg_send_eintr RG) 1); [unfold G_DR, G_SL; w_infp | lia].
- left. apply (GD (as_errno B) 4); [unfold G_DR, G_SL; w_infp | lia].
- destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  right. exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity | lia].
Qed.

(* the relay entry's 56 bytes after the two stores (s->skip, s->used), every other field kept *)
Lemma rs_entry_store_x : forall (W : world SEGS) m m' SA e e',
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_pad1 e' = re_pad1 e -> re_buf e' = re_buf e ->
re_cap e' = re_cap e -> re_hp e' = re_hp e -> re_keys e' = re_keys e -> re_pad2 e' = re_pad2 e ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat -> 0 <= re_skip e' < 2 ^ 32 -> 0 <= re_used e' < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m') (SA + 8) 4 (re_skip e') ->
val_mem SEGS (arm W m') (SA + 24) 8 (re_used e') ->
(forall x, SA <= x < SA + 8 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 12 <= x < SA + 24 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 32 <= x < SA + 56 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes e')).
Proof.
intros W m m' SA e e' Efd Eeof Ep1 Ebuf Ecap Ehp Ekeys Ep2 Hp1 Hp2 Hsk Hus H Vsk Vus K1 K2 K3.
assert (Enh : re_nheld e' = re_nheld e) by (unfold re_nheld; rewrite Ekeys; reflexivity).
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Ep1, Ebuf, Ecap, Ehp, Enh, Ep2.
rewrite (rs_le4_bytes_x (re_skip e') Hsk), (rs_le8_bytes_x (re_used e') Hus).
rewrite !rs_bzs_app_x in H |- *.
apply garr8_app in H as [H1 H]. apply garr8_app in H as [H2 H]. apply garr8_app in H as [_ H].
apply garr8_app in H as [H4 H]. apply garr8_app in H as [H5 H]. apply garr8_app in H as [_ H].
apply garr8_app in H as [H7 H]. apply garr8_app in H as [H8 H]. apply garr8_app in H as [H9 H10].
apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split;
  [|apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split;
  [|apply garr8_app; split; [|apply garr8_app; split; [|apply garr8_app; split]]]]]]]].
- apply (rs_garr8_kept_x W m W m'); [exact H1 | intros x Hx; apply K1; rs_len_in Hx; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H2); rs_len; lia | intros x Hx; apply K1; rs_len_in Hx; lia].
- apply (rs_garr8_at_x _ (SA + 8)); [apply rs_garr8_of_val_x; [change (8 * Z.of_nat 4) with 32; lia | exact Vsk] | rs_len; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H4); rs_len; lia | intros x Hx; apply K2; rs_len_in Hx; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H5); rs_len; lia | intros x Hx; apply K2; rs_len_in Hx; lia].
- apply (rs_garr8_at_x _ (SA + 24)); [apply rs_garr8_of_val_x; [change (8 * Z.of_nat 8) with 64; lia | exact Vus] | rs_len; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H7); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H8); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H9); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
- apply (rs_garr8_kept_x W m W m'); [apply (rs_garr8_at_x _ _ _ _ H10); rs_len; lia | intros x Hx; apply K3; rs_len_in Hx; lia].
Qed.

(* the relay entry with new s->skip, s->used and buffer contents: the line loop's form *)
Lemma rs_okx_new_x : forall ly S (W : world SEGS) m m' e e',
aentry_okx B ly S W m e ->
re_eof e' = re_eof e -> re_pad1 e' = re_pad1 e -> re_pad2 e' = re_pad2 e -> re_fd e' = re_fd e ->
re_cap e' = re_cap e -> re_buf e' = re_buf e -> re_hp e' = re_hp e -> re_kh e' = re_kh e -> re_keys e' = re_keys e ->
(re_skip e' = 0 \/ re_skip e' = 1) ->
Z.of_nat (length (re_U e')) = re_used e' -> re_used e' <= re_cap e' -> 0 < re_cap e ->
Z.of_nat (length (re_junk e')) = re_cap e' - re_used e' ->
garr8 SEGS (arm W m') (re_buf e') (bzs (re_U e' ++ re_junk e')) ->
(forall q n x, In (q, n) ((if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
     map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
   q <= x < q + n -> abyte_kept W m W m' x) ->
aentry_okx B ly S W m' e'.
Proof.
intros ly S W m m' e e' (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14)
  Eeof Ep1 Ep2 Efd Ecap Ebuf Ehp Ekh Ekeys Hsk HU Huc Hcp HJ HGB KB.
assert (Enh : re_nheld e' = re_nheld e) by (unfold re_nheld; rewrite Ekeys; reflexivity).
rewrite Ecap in Huc, HJ. rewrite Ebuf in HGB.
unfold aentry_okx. rewrite Eeof, Ep1, Ep2, Efd, Ecap, Ebuf, Ehp, Ekh, Enh, Ekeys.
split; [exact K1|]. split; [exact Hsk|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
split; [exact K6|]. split; [exact HU|]. split; [exact Huc|].
split.
{ right. destruct K9 as [(C0 & _)|(Cp & BI & _)]; [lia|].
  split; [exact Cp|]. split; [exact BI|]. split; [exact HJ | exact HGB]. }
split; [exact K10|].
split.
{ destruct K11 as [Z0|(HI & HF & H8 & H8' & HBp)]; [left; exact Z0 | right].
  split; [exact HI|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
  apply (akept_garr8 W m); [|exact HBp].
  intros x Hx. apply (KB (re_hp e) (re_kh e)); [rewrite (proj2 (Z.eqb_neq _ 0) HI); left; reflexivity |].
  unfold bzs in Hx. rewrite length_map, rs_key_ptrs_len_x in Hx. unfold re_nheld in H8. lia. }
split; [exact K12|]. split; [exact K13|].
rewrite Forall_forall in K14 |- *. intros k Hk. destruct (K14 k Hk) as (P1 & P2 & P3 & P4).
split; [exact P1|]. split; [|split; [exact P3 | exact P4]].
apply (akept_garr8 W m); [|exact P2]. intros x Hx.
apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
- apply in_or_app. right. exact (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) _ _ Hk).
- unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.



(* ---- route R: the R twin of each piece of Section cx whose statement names the journal, SRr, a carrier or
   a statement: the strict text with the journal and SRr at R and each carrier / statement / engine lemma at its R
   twin (W_drain_cx_x.v Section wR). The strict lemmas above are unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Theorem dr_rest_xR : dr_rest_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr s1 D p W1 c1 HB HLR Hdi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DLR_xR in HLR.
destruct HLR as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent
  & jb & a & o & ha & ks & tl & Hc1 & Hregs & Hs8 & Hs9 & Hs10 & Hbnd & Hnonul & HDLC & Hfut).
destruct Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
unfold dr_frame in HFR. cbv zeta in HFR.
destruct HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224
  & F216 & F176 & Hsaved).
unfold DLC_xR, LCORE_xR in HDLC.
destruct HDLC as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
unfold DMEM_xR in HMEM.
destruct HMEM as (HJ & HROM & HPRES & HFRAMES & HFR2 & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (HPRE0 & HSA0 & HGin0 & HGSA & HSAG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof HPRE0 as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HGin1) as (_ & HG4096 & HGceil & HGapp & _).
rewrite RQ in HGceil, HGapp.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
clear memS HJi.
set (SA := dxSA cx) in *.
unfold AENT, ATABLE in *.
assert (HSAb : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by lia.
assert (Hsk01 : 0 <= re_skip e1 <= 1) by (destruct HOKX as (_ & X & _); clear - X; lia).
assert (Hsp' : alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\
  spZ regs1 mod 16 = 0).
{ rewrite Hsp. unfold DRAIN_FRAME in *. repeat split; try lia. rewrite Zminus_mod, Hal16. reflexivity. }
(* ---- the relay's buffer: a live block of cap in {8192, 16384} bytes, apart from the table ---- *)
assert (HCAP : re_cap e1 = drain_b_c.ds_cap s1) by (destruct HLINK as (X & _); exact X).
assert (HUW : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & X & _); exact X).
pose proof HRST as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & K7 & K8 & K9 & _).
assert (HLW : length (dW s1) = length (re_U e1)) by (rewrite <- HUW; apply rs_bzs_len_x).
assert (HCAPb : 4096 <= re_cap e1) by (clear - RS_gr HCAP; unfold ulen in RS_gr; lia).
destruct K9 as [(Hc0 & _)|(Hcp & HBin & HJlen & HBUFG)]; [clear - Hc0 HCAPb; lia|].
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - HCAPb; lia); reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HBin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
rewrite RQB in Hbceil, Hbapp, Hbpres.
pose proof Hbnd as (Hbp & _).
pose (NN := Z.of_nat (length (dW s1) - p)).
assert (HNN : 0 <= NN /\ Z.of_nat p + NN = re_used e1) by (unfold NN; clear - HLW K7 Hbp; lia).
assert (HTB : rs_hide (dxG cx + 896 <= re_buf e1 \/ re_buf e1 + re_cap e1 <= dxG cx)).
{ pose proof (rs_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR HGin1 HBin ltac:(intros X; injection X; clear - HCAPb; lia)) as X.
  rewrite RQ, RQB in X. exact X. }
pose proof (Permutation_NoDup HPERM (rs_ablocks_nodup_x _ _ _ _ _ _ HAR)) as HNDp.
unfold aentry_blks in HNDp. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in HNDp by lia. cbn [app] in HNDp.
apply List.NoDup_cons_iff in HNDp as [HGnot HNDp]. apply List.NoDup_cons_iff in HNDp as [Hbufnot HNDp].
(* ---- FIN: the loop's top in the round state dnext s1, from the memory after the segment (plain drain_b.v FIN
   in rest_step).  Only s->skip, s->used, the first NN bytes of the buffer and the callee's scratch below the
   frame changed; presence only grew. ---- *)
lazymatch goal with |- SRrG _ _ _ _ ?QPOST =>
assert (FIN : forall regs4 mem4 md4 used' sk',
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mem4 md4 k1 ->
  dregs_top RG cx regs4 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
     ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mem4 x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) mem4 x) ->
  val_mem SEGS (arm W1 mem4) (SA + 24) 8 used' ->
  val_mem SEGS (arm W1 mem4) (SA + 8) 4 sk' ->
  (forall i, 0 <= i < NN -> aview SEGS (w_H W1) mem4 (re_buf e1 + i) =
                            aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)) ->
  rs_hide ((NN < 6001 /\ used' = NN /\ sk' = re_skip e1) \/ (6001 <= NN /\ used' = 0 /\ sk' = 1)) ->
  SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_top) regs4 mem4 md4) QPOST) end.
{ intros regs4 mem4 md4 used' sk' HJ4 HR4 KEEP PRES VU VS VB BR4. apply Hdi.
  (* ---- the model: no line from p on; chunk keeps skipn p W or resets it ---- *)
  pose proof RS_J1 as (_ & _ & _ & NZU).
  pose proof (rm_drlq_nil s1 p Hbnd Hnonul) as DQ.
  pose proof (rm_drl s1 p NZU Hbnd Hnonul) as DRL.
  assert (LSK : Z.of_nat (length (skipn p (dW s1))) = NN) by (rewrite length_skipn; reflexivity).
  assert (LL : Z.of_nat LINE_LIMIT = 6000) by reflexivity.
  assert (CK2 : drl s1 = lines (drain_b_c.ds_ref s1) (ddata s1) /\
    J1 (fst (fst (dchunk s1))) (snd (fst (dchunk s1))) (feed (drain_b_c.ds_ref s1) (ddata s1))).
  { pose proof (chunk_ok (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) (ddata s1) RS_J1) as CK.
    unfold drl, dchunk. destruct (chunk (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as [[u'' sk''] ls].
    cbv beta iota in CK. exact CK. }
  assert (LINES : lines (dSTR cx) (D ++ ddata s1) = lines (dSTR cx) D ++ drlp s1 p).
  { rewrite lines_app, <- RS_ref, <- (proj1 CK2), DRL. reflexivity. }
  assert (EH : drain_b_c.ds_H (dnext (dlive cx) (dxmx cx) s1) = dlH cx s1 p)
    by (unfold dnext, dlH, dlrun; cbn [drain_b_c.ds_H]; rewrite DRL; reflexivity).
  assert (EKA : drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1) = dlka cx s1 p)
    by (unfold dnext, dlka, dlrun; cbn [drain_b_c.ds_ka]; rewrite DRL; reflexivity).
  assert (EOC : drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) = dloc cx s1 p)
    by (unfold dnext, dloc, dlrun; cbn [drain_b_c.ds_ocap]; rewrite DRL; reflexivity).
  assert (ENO : drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) = dlno s1 p)
    by (unfold dnext, dlno; cbn [drain_b_c.ds_no]; rewrite DRL; reflexivity).
  (* ---- what the segment kept ---- *)
  assert (HSPb' : alloc_ceiling + 16848 <= dsp0 cx) by (unfold DRAIN_FRAME in *; lia).
  assert (HSPt : dsp0 cx <= 2 ^ 47) by (rewrite Hsp in Hsp'; unfold DRAIN_FRAME in *; lia).
  assert (NNC : NN <= re_cap e1) by (clear - HNN K8; lia).
  assert (KK : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
     ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
     abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx N1 N2 N3 N4. split; [exact (KEEP x Hx N1 N2 N3 N4)|].
    intros Hw. exact (writable_kept (w_H W1) m1 mem4 x (PRES x) Hw). }
  (* an image byte lies in no live block (the laws' client-image field), so neither the table nor the buffer *)
  assert (KBand : forall x, in_img SEGS x -> abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx. pose proof (pa_img_range x Hx) as Hb.
    assert (NG : ~ (dxG cx <= x < dxG cx + 896)).
    { intros Hr. apply (rs_blk_noimg_x _ _ _ _ _ _ _ _ x HAR HGin1); [rewrite RQ; exact Hr | exact Hx]. }
    assert (NB : ~ (re_buf e1 <= x < re_buf e1 + re_cap e1)).
    { intros Hr. apply (rs_blk_noimg_x _ _ _ _ _ _ _ _ x HAR HBin); [rewrite RQB; exact Hr | exact Hx]. }
    apply KK; clear - Hb NG NB HGSA HSAG NNC HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia. }
  (* g_s is part of G_DR, whose bytes are image bytes (HG) *)
  assert (GSI : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> in_img SEGS x).
  { intros x Hx. refine (proj1 (HG x _)). unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
  assert (KFR : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 mem4 x).
  { intros x Hx. apply KK; clear - Hx HSPb' HSPt Hbceil NNC HSAb; unfold ESTACK, DRAIN_FRAME in *; lia. }
  lazymatch type of Hbufnot with ~ In _ ?RR0 =>
  assert (RRab : forall b, In b RR0 -> In b (ablocks B ly1 S1));
  [ intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; unfold aentry_blks;
    rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - Hcp; lia); right; exact Hb
  | assert (KB : forall q m x, In (q, m) RR0 -> q <= x < q + m -> abyte_kept W1 m1 W1 mem4 x) ] end.
  { intros q m x Hq Hx.
    pose proof (RRab _ Hq) as Hab.
    assert (Nb : (q, m) <> (re_buf e1, re_cap e1)) by (intros E; apply Hbufnot; rewrite <- E; exact Hq).
    assert (Ng : (q, m) <> (dxG cx, 896)) by (intros E; apply HGnot; right; rewrite <- E; exact Hq).
    pose proof (rs_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hab HBin Nb) as A1. rewrite RQB in A1.
    pose proof (rs_blk_apart_x _ _ _ _ _ _ _ _ _ _ HAR Hab HGin1 Ng) as A2. rewrite RQ in A2.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & Hq4096 & Hqceil & _ & _ & _).
    pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hab) as Hm0.
    pose proof (req_size_pos m ltac:(clear - Hm0; lia)) as (_ & Hmr).
    apply KK; clear - Hx A1 A2 Hqceil Hm0 Hmr HGSA HSAG NNC HSPb' Hq4096 C1; unfold ESTACK, DRAIN_FRAME; lia. }
  (* ---- the buffer after the move-down ---- *)
  assert (LU : length (re_U e1) = (p + Z.to_nat NN)%nat) by (unfold NN; clear - HLW Hbp K7; lia).
  assert (LUJ : length (re_U e1 ++ re_junk e1) = Z.to_nat (re_cap e1))
    by (rewrite length_app; clear - K7 HJlen K8; lia).
  assert (LB1' : length (skipn p (re_U e1)) = Z.to_nat NN) by (rewrite length_skipn; clear - LU; lia).
  set (BUFB := skipn p (re_U e1) ++ skipn (Z.to_nat NN) (re_U e1 ++ re_junk e1)).
  assert (LBUF : length BUFB = Z.to_nat (re_cap e1))
    by (unfold BUFB; rewrite length_app, LB1', length_skipn, LUJ; clear - NNC HNN; lia).
  assert (GBUF : garr8 SEGS (arm W1 mem4) (re_buf e1) (bzs BUFB)).
  { unfold BUFB. rewrite rs_bzs_app_x. apply garr8_app. split.
    - pose proof HBUFG as G0. rewrite rs_bzs_app_x in G0. apply garr8_app in G0 as [GU _].
      pose proof (rs_garr8_skipn_x _ _ _ p GU ltac:(rewrite rs_bzs_len_x; clear - LU; lia)) as GS.
      rewrite rs_skipn_bzs_x in GS.
      apply (rs_garr8_move_x _ _ _ _ _ GS). intros j Hj. rewrite rs_bzs_len_x, LB1' in Hj.
      unfold arm. apply rs_mbyte_of_aview2_x. rewrite (VB (Z.of_nat j) ltac:(clear - Hj HNN; lia)). reflexivity.
    - rewrite rs_bzs_len_x, LB1'.
      pose proof (rs_garr8_skipn_x _ _ _ (Z.to_nat NN) HBUFG ltac:(rewrite rs_bzs_len_x, LUJ; clear - NNC HNN; lia)) as GR.
      rewrite rs_skipn_bzs_x in GR.
      apply (rs_garr8_kept_x W1 m1 W1 mem4 _ _ GR). intros x Hx. rewrite rs_bzs_len_x, length_skipn, LUJ in Hx.
      unfold rs_hide in HTB.
      apply KEEP; clear - Hx HTB NNC HNN HGSA HSAG Hbceil HSPb' Hb4096 C1; unfold ESTACK, DRAIN_FRAME; lia. }
  (* ---- the two arms: s->used, s->skip and the buffer's live part ---- *)
  assert (HBR : (Z.of_nat (length (firstn (Z.to_nat used') BUFB)) = used' /\
     bzs (firstn (Z.to_nat used') BUFB) = drain_b_c.ds_u (dnext (dlive cx) (dxmx cx) s1) /\
     sk' = (if drain_b_c.ds_skip (dnext (dlive cx) (dxmx cx) s1) then 1 else 0) /\
     ~ In (Z_to_bv 8 0) (firstn (Z.to_nat used') BUFB)) /\
     0 <= used' <= 6000 /\ used' <= re_cap e1 /\ rs_hide (sk' = 0 \/ sk' = 1)).
  { unfold rs_hide in BR4 |- *. destruct BR4 as [(HA & -> & ->)|(HB' & -> & ->)].
    - assert (FA : firstn (Z.to_nat NN) BUFB = skipn p (re_U e1)).
      { unfold BUFB. rewrite firstn_app, LB1', Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
        apply firstn_all2. rewrite LB1'. lia. }
      assert (LEN : (length (skipn p (dW s1)) <= LINE_LIMIT)%nat)
        by (apply Nat2Z.inj_le; rewrite LSK, LL; clear - HA; lia).
      destruct (rm_dnext_short (dlive cx) (dxmx cx) s1 p NZU Hbnd Hnonul LEN) as [E1 E2].
      rewrite FA, E1, E2. split; [split; [|split; [|split]]|split; [|split]].
      + rewrite LB1'. clear - HNN. lia.
      + rewrite <- rs_skipn_bzs_x, HUW. reflexivity.
      + exact (proj1 (proj2 (proj2 HLINK))).
      + apply rs_nz_in_x. rewrite <- rs_skipn_bzs_x, HUW. exact (rm_nz_rest s1 p Hnonul).
      + clear - HA HNN. lia.
      + exact NNC.
      + destruct HOKX as (_ & X & _). exact X.
    - assert (LEN : (LINE_LIMIT < length (skipn p (dW s1)))%nat)
        by (apply Nat2Z.inj_lt; rewrite LSK, LL; clear - HB'; lia).
      destruct (rm_dnext_long (dlive cx) (dxmx cx) s1 p NZU Hbnd Hnonul LEN) as [E1 E2].
      rewrite E1, E2. cbn [Z.to_nat firstn length bzs map]. split; [split; [|split; [|split]]|split; [|split]].
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + intros [].
      + lia.
      + clear - Hcp. lia.
      + right. reflexivity. }
  destruct HBR as ((FUL & FU & FSK & FNZ) & FUB & FUC & FSK01).
  assert (FJL : Z.of_nat (length (skipn (Z.to_nat used') BUFB)) = re_cap e1 - used')
    by (rewrite length_skipn, LBUF; clear - FUB FUC; lia).
  (* ---- the relay entry after the segment, and the rounds still to come ---- *)
  set (e' := RE (re_fd e1) (re_eof e1) sk' (re_pad1 e1) (re_buf e1) used' (re_cap e1) (re_hp e1) (re_kh e1)
    (re_pad2 e1) (re_keys e1) (firstn (Z.to_nat used') BUFB) (skipn (Z.to_nat used') BUFB)).
  pose proof Hfut as Hfut'. rewrite DQ in Hfut'. unfold dlfut in Hfut'. cbn [drain_b_c.lines_run fst snd] in Hfut'.
  destruct Hfut' as (tl2 & Hlat & Htl). cbn [app] in Htl. subst tl.
  unfold DI_xR.
  lazymatch type of Hlat with dlater _ _ ?jb' ?a' _ =>
  exists regs4, ly1, S1, Hp1, mem4, md4, k1, e', h1, out1, ev1, LB1, spent, jb', a', tl2 end.
  split; [reflexivity|]. split; [exact HR4|].
  split.
  { unfold DMEM_xR.
    split; [exact HJ4|].
    split.
    { intros x Hx. rewrite (proj1 (KBand x (rs_rom_img_x x Hx))). exact (HROM x Hx). }
    split.
    { intros x H1 H2 H3 Hpr. apply PRES. exact (HPRES x H1 H2 H3 Hpr). }
    split; [exact HFRAMES|].
    split.
    { assert (VMF : forall a0 n v, dsp0 cx - DRAIN_FRAME <= a0 -> a0 + Z.of_nat n <= dsp0 cx ->
        val_mem SEGS (arm W1 m1) a0 n v -> val_mem SEGS (arm W1 mem4) a0 n v).
      { intros a0 n v H1 H2 Hv. apply (akept_vm W1 m1 W1 mem4 a0 n v); [|exact Hv].
        intros y Hy. apply KFR. clear - H1 H2 Hy. lia. }
      unfold dr_frame. cbv zeta. change (dxSA cx) with SA.
      repeat (split; [apply VMF; [unfold DRAIN_FRAME; lia | unfold DRAIN_FRAME; lia | assumption]|]).
      intros i Hi. apply VMF; [unfold DRAIN_FRAME; lia | unfold DRAIN_FRAME; clear - Hi; lia | exact (Hsaved i Hi)]. }
    split.
    { apply (rs_entry_store_x W1 m1 mem4 SA e1 e'); try reflexivity.
      - destruct HOKX as (_ & _ & X & _). exact X.
      - destruct HOKX as (_ & _ & _ & X & _). exact X.
      - change (0 <= sk' < 2 ^ 32). unfold rs_hide in FSK01. clear - FSK01. lia.
      - change (0 <= used' < 2 ^ 64). clear - FUB. lia.
      - exact HENT.
      - exact VS.
      - exact VU.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia.
      - intros x Hx. unfold rs_hide in HTB.
        apply KEEP; clear - Hx HTB HGSA HSAG NNC HNN HSAb HSPb' C1; unfold ESTACK, DRAIN_FRAME; lia. }
    split.
    { intros i Hi. apply (writable_kept (w_H W1) m1 mem4 _ (PRES _)). exact (HAWR i Hi). }
    split.
    { apply (rs_okx_new_x ly1 S1 W1 m1 mem4 e1 e' HOKX); try reflexivity.
      - unfold rs_hide in FSK01. exact FSK01.
      - exact FUL.
      - exact FUC.
      - exact Hcp.
      - exact FJL.
      - change (garr8 SEGS (arm W1 mem4) (re_buf e1)
          (bzs (firstn (Z.to_nat used') BUFB ++ skipn (Z.to_nat used') BUFB))).
        rewrite firstn_skipn. exact GBUF.
      - intros q n x Hq Hx. apply (KB q n x); [apply in_or_app; left; exact Hq | exact Hx]. }
    split.
    { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _).
      eapply asrc_at_kept; [exact HSRC | |
        intros b Hb; apply RRab; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (rs_asrc_fp_in_x _ _ _ _ _ _ HSRC r Hr x Hx) as [Hg | (q & m & Hq & Hqx)].
      - apply KBand, GSI. unfold dHA, ASRC in *. clear - Hg Hj4. lia.
      - apply (KB q m x); [apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx]. }
    split.
    { intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & V1 & V2 & Ho). exists f, o'.
      pose proof HGSB as (G1 & G2 & _). unfold ASRC in *.
      split; [|split; [|exact Ho]];
        (apply (akept_vm W1 m1); [intros y Hy; apply KBand, GSI; clear - Hy Hi; lia | assumption]). }
    split.
    { intros x Hx Hn. apply (rs_abyte_trans_x _ _ _ _ _ _ x (HKEPT x Hx Hn)).
      apply KBand, GSI. exact Hx. }
    split.
    { rewrite LINES, ENO, EOC.
      eapply aout_at_kept; [exact HOUT | |
        intros b Hb; apply RRab; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (rs_aout_fp_in_x _ _ r Hr x Hx) as [Hb | (q & m & Hq & Hqx)].
      - exact (KBand x Hb).
      - apply (KB q m x); [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hq | exact Hqx]. }
    split.
    { intros Hl. rewrite EOC. exact (HLIVE Hl). }
    rewrite EOC. exact HPERM. }
  split; [exact FNZ|]. split; [change (used' <= APARTIAL); unfold APARTIAL; clear - FUB; lia|].
  split.
  { unfold DLINK. pose proof HLINK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
    destruct (dneed_dnext (dlive cx) (dxmx cx) s1 RS_gr RS_pe RS_wf RS_st RS_ei) as [_ WFn].
    split; [exact HCAP|]. split; [exact FU|]. split; [exact FSK|].
    split; [rewrite EH; exact L4|]. split; [rewrite EKA; exact L5|].
    split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|].
    split; [exact L10|]. split; [exact L11 | exact WFn]. }
  split; [exact HSAME|].
  split.
  { rewrite LINES. pose proof HHIST as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    unfold DHIST. rewrite EH, ENO. rewrite DQ in H10. cbn [length Z.of_nat] in H10.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
    split; [exact H10 | exact H11]. }
  split; [exact (proj2 CK2)|].
  split; [exact Hlat | exact HBUD]. }
pose proof (rs_entry_x W1 regs1 m1 SA (re_skip e1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  R27 R21 ltac:(lia) ltac:(rewrite Hsp; exact M64) ltac:(rewrite Hsp; exact F160) ltac:(rewrite Hsp; exact F176)
  ltac:(rewrite Hsp; exact F184) ltac:(rewrite Hsp; exact M192) ltac:(rewrite Hsp; exact M200)
  ltac:(rewrite Hsp; exact F208) ltac:(rewrite Hsp; exact F224)
  ltac:(apply rs_entry_skip_x; [lia | exact HENT]) HAWR) as HS.
subst c1. unfold cfg_at.
remember (Eimg (Ereg regs1 (rs_extra SA (re_skip e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_skip e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (SA + 32)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (shadow_addr SA))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (USA : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS RBx rs_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) m1 E RBx 32%nat SA 56 SA 0 56).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) 896); [exact HAR | exact HGin1 | lia |].
    rewrite RQ. lia.
  - unfold RBx. apply (U_atom E 21 SHADOW_OFF); [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | unfold SHADOW_OFF; lia].
  - apply (U_atom E 32 SA E32). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. unfold AENT in *. lia. }
paj_run_tok_xR RUNR HS HJ SHOK RBspan.
{ cbn [ss_mem ss_rs rs_regions].
  apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  all: (intros x Hx; cbn [rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USA in Hx;
    left; (split; [|lia]); right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
    | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
rename ms into msT.
lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGT end.
rename HF into HFT, HFr into HFrT.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
(* what the first run kept: everything but s->skip and s->used *)
assert (KT : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem msT) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. apply (aview_kept_out E (ss_mem ss_rs) (w_H W1) m1 (ms_mem msT) HFrT x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_rs rs_regions In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [rs_frame rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?USA in Hr; lia. }
assert (HART : ARx ly1 S1 Hp1 W1 (ms_mem msT) (with_vm_backing (m_vm_lazy md1) mat md1))
  by (eapply ajournal_gx_AR_xR; exact HJ).
assert (Gbuf : forall x, re_buf e1 <= x < re_buf e1 + re_cap e1 -> ~ in_img SEGS x)
  by (intros x Hx; apply (rs_blk_noimg_x _ _ _ _ _ _ _ _ x HAR HBin); rewrite RQB; lia).
assert (Gtab : forall x, dxG cx <= x < dxG cx + 896 -> ~ in_img SEGS x)
  by (intros x Hx; apply (rs_blk_noimg_x _ _ _ _ _ _ _ _ x HAR HGin1); rewrite RQ; lia).
assert (HROMT : rom_view SEGS W1 (ms_mem msT)).
{ intros x Hx. pose proof (rs_rom_img_x x Hx) as Hi. pose proof (Hsegs x Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite KT; [exact (HROM x Hx) | lia | intros Hw; apply (Gtab x); [lia | exact Hi] | intros Hw; apply (Gtab x); [lia | exact Hi]]. }
assert (HSPb : alloc_ceiling + 16848 <= dsp0 cx) by (unfold DRAIN_FRAME in *; lia).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_asan_memmove)
    (fun x => re_buf e1 <= x < re_buf e1 + NN)
    (fun regs' mem' => getr regs' 10 = w64 (re_buf e1) /\
       forall i, 0 <= i < NN -> aview SEGS (w_H W1) mem' (re_buf e1 + i) =
                                aview SEGS (w_H W1) (ms_mem msT) (re_buf e1 + Z.of_nat p + i))
    W1 (ms_regs msT) (ms_mem msT) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ).
  - unfold spZ at 1. rewrite Q2, Usp, Hsp. lia.
  - unfold DRAIN_FRAME. reflexivity.
  - unfold DRAIN_FRAME. lia.
  - lia.
  - rewrite HDS. unfold ESTACK, DRAIN_FRAME. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp0.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp0.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros x. destruct (Z_le_gt_dec (re_buf e1) x); destruct (Z_lt_ge_dec x (re_buf e1 + NN));
      [left; lia | right; lia | right; lia | right; lia].
  - intros x Hx Hg. exfalso. apply (Gbuf x); [lia | exact (proj1 (HG x Hg))].
  - intros x Hx Hng. split; [|lia].
    assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
    destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnot0].
    + right. left. split.
      * apply (Permutation_in _ HPERM0) in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|Hin0];
          [injection X as X1 X2; clear - X2 HCAPb; lia|].
        assert (Hin3 : In (re_buf e1, re_cap e1) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
        { apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; left; exact X|].
          apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; left; exact X|].
          apply in_app_or in Hin0 as [X|Hin0]; [apply in_or_app; right; apply in_or_app; right; exact X|].
          exfalso. apply Hbufnot. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
          exact Hin0. }
        unfold dFP, dr_fp. apply inFP_cons. right. exists (re_buf e1, re_buf e1 + req_size (re_cap e1)).
        split; [unfold ablocks_fp; exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ _ Hin3)|].
        cbn [fst snd]. rewrite RQB. lia.
      * exists (re_buf e1), (re_cap e1). split; [exact HBin | rewrite RQB; lia].
    + right. right. left. exists (re_buf e1), (re_cap e1). split; [exact HBin|]. split; [exact Hnot0 | rewrite RQB; lia].
  - intros HPRE HSC.
    apply (AMEMMOVE ly1 S1 Hp1 W1 (ms_regs msT) (ms_mem msT) _ (re_buf e1) (re_buf e1 + Z.of_nat p) NN HPRE).
    + rewrite Q10, (EE 26%nat 26%bv eq_refl). exact Hs10.
    + rewrite Q11, (EE 24%nat 24%bv eq_refl). exact Hs8.
    + rewrite Q12, (EE 25%nat 25%bv eq_refl). exact Hs9.
    + split; [lia|]. assert (HCAPu : re_cap e1 <= 16384)
        by (destruct HOKX as (_ & _ & _ & _ & _ & X & _); clear - X; lia). lia.
    + lia.
    + lia.
    + intros x Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HART HBin) as (_ & _ & _ & _ & HP & _).
      rewrite RQB in HP. destruct (HP x ltac:(lia)) as [HPx HPo].
      split; [exact (apresent_writable SEGS _ _ _ HPx)|]. split; [exact HPo|].
      unfold spZ. rewrite Q2, Usp, Hsp. unfold ESTACK, DRAIN_FRAME. lia.
    + apply (rs_amem_range_blk_x _ _ _ _ _ _ _ _ _ _ HART HBin); [lia | lia | rewrite RQB; lia].
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros Hn. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HART HBin);
        [lia | rewrite RQB; lia | exact Hn].
    + lia.
    + lia.
    + intros x Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HART HBin) as (_ & _ & _ & _ & HP & _).
      rewrite RQB in HP. destruct (HP x ltac:(lia)) as [HPx _].
      split; [exact (aview_some_of_apresent SEGS _ _ _ HPx)|].
      unfold spZ. rewrite Q2, Usp, Hsp. unfold ESTACK, DRAIN_FRAME. lia.
    + apply (rs_amem_range_blk_x _ _ _ _ _ _ _ _ _ _ HART HBin); [lia | lia | rewrite RQB; lia].
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros Hn. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 _ _ _ _ _ _ _ _ _ _ HART HBin);
        [lia | rewrite RQB; lia | exact Hn].
    + exact HROMT.
    + intros Hn. split.
      * apply (rs_amem_near_x _ _ _ _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
      * apply (rs_amem_near_x _ _ _ _ _ _ _ _ _ HART HBin); [lia | rewrite RQB; lia].
    + intros x Hx Hr. apply (Gbuf x); [lia | exact Hr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HR10 & HMV) & Hfr2 & Hpres2).
assert (TBX : forall x, dxG cx <= x < dxG cx + 896 -> ~ (re_buf e1 <= x < re_buf e1 + NN))
  by (intros x Hx Hb; unfold rs_hide in HTB; clear - Hx Hb HTB HNN K8; lia).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (RK : forall x, 0 <= x < 2 ^ 64 -> ~ (re_buf e1 <= x < re_buf e1 + NN) ->
    ~ (dsp0 cx + - DRAIN_FRAME - ESTACK <= x < dsp0 cx + - DRAIN_FRAME) ->
    mbyte SEGS (mrestrict (w_H W1) mem2) x = mbyte SEGS (mrestrict (w_H W1) (ms_mem msT)) x).
  { intros x Hx N1 N2. apply (mbyte_of_aview SEGS). exact (Hfr2 x Hx N1 N2). }
  assert (WK : forall x, writable_at SEGS (mrestrict (w_H W1) (ms_mem msT)) x ->
    writable_at SEGS (mrestrict (w_H W1) mem2) x)
    by (intros x Hw; exact (writable_kept (w_H W1) (ms_mem msT) mem2 x (fun Hp => Hpres2 _ Hp) Hw)).
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [rs_frame rs_skip rs_used YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?Usp, ?USA; unfold ESTACK, DRAIN_FRAME in *.
  - intros x Hx. apply RK; lia.
  - intros x Hx. lia.
  - intros x Hx. apply RK; [lia | apply TBX; lia | lia].
  - intros x _ Hw. exact (WK x Hw).
  - intros x Hx. apply RK; [lia | apply TBX; lia | lia].
  - intros x _ Hw. exact (WK x Hw). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs1) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp).
assert (USAa : bv_unsigned (ew Ea 32) = SA) by (rewrite (OLDa 32%nat ltac:(lia)); exact USA).
assert (HAR2 : ARx ly1 S1 Hp1 W1 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
assert (SHOK2 : sh_ok SEGS RBx rs_SH Ea (mrestrict (w_H W1) mem2)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea RBx 32%nat SA 56 SA 0 56).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mem2 md2 (dxG cx) 896); [exact HAR2 | exact HGin1 | lia |].
    rewrite RQ. lia.
  - unfold RBx. apply (U_atom Ea 21 SHADOW_OFF);
      [rewrite (OLDa 21%nat ltac:(lia)), (EE 21%nat 21%bv eq_refl), R21; reflexivity | unfold SHADOW_OFF; lia].
  - apply (U_atom Ea 32 SA); [rewrite (OLDa 32%nat ltac:(lia)); exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
paj_run_tok_xR RUNR HS HJ2 SHOK2 RBspan.
{ apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  all: (intros x Hx; cbn [rs_skip rs_used YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
    left; (split; [|lia]); right; left; split;
    [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
    | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
rename ms into ms2.
lazymatch goal with H : mem_grows (mrestrict _ mem2) _ |- _ => rename H into HG2 end.
rename HF into HF2, HFr into HFr2.
assert (K2 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  aview SEGS (w_H W1) (ms_mem ms2) x = aview SEGS (w_H W1) mem2 x).
{ intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms2) HFr2 x Hx).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
assert (E25 : ew Ea 25 = Z_to_bv 64 NN) by (rewrite (OLDa 25%nat ltac:(lia)), (EE 25%nat 25%bv eq_refl); exact Hs9).
(* the memory after the second run, against the segment's entry *)
assert (TBX' : forall x, SA <= x < SA + 56 -> ~ (re_buf e1 <= x < re_buf e1 + NN)) by (intros x Hx; apply TBX; lia).
assert (KM2 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
  ~ (re_buf e1 <= x < re_buf e1 + NN) -> ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem ms2) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2 N3 N4. rewrite (K2 x Hx N1 N2), (Hfr2 x Hx N3 ltac:(lia)). exact (KT x Hx N1 N2). }
assert (PM2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms2) x).
{ intros x Hx. apply (apresent_grows _ _ _ _ HG2). apply Hpres2. exact (apresent_grows _ _ _ _ HGT Hx). }
assert (VB2 : forall i, 0 <= i < NN -> aview SEGS (w_H W1) (ms_mem ms2) (re_buf e1 + i) =
  aview SEGS (w_H W1) m1 (re_buf e1 + Z.of_nat p + i)).
{ intros i Hi.
  assert (NB : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> ~ (SA <= y < SA + 56)).
  { intros y Hy Hs. unfold rs_hide in HTB. clear - Hy Hs HTB HGSA HSAG. lia. }
  rewrite (K2 (re_buf e1 + i) ltac:(lia) ltac:(intros X; apply (NB (re_buf e1 + i)); lia)
    ltac:(intros X; apply (NB (re_buf e1 + i)); lia)).
  rewrite (HMV i Hi).
  exact (KT (re_buf e1 + Z.of_nat p + i) ltac:(lia) ltac:(intros X; apply (NB (re_buf e1 + Z.of_nat p + i)); lia)
    ltac:(intros X; apply (NB (re_buf e1 + Z.of_nat p + i)); lia)). }
psrr_branch_tok RUN BRR HS SHOK2 RBspan.
- rewrite branch_ltu_U, (U_atom Ea 25 NN E25), (U_lit Ea 6001) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 RBspan A_dr_top.
  { apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    all: (intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
      left; (split; [|lia]); right; left; split;
      [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
      | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
  rename ms into ms3.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem ms2)) _ |- _ => rename H into HG3 end.
  rename HF into HF3, HFr into HFr3.
  assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
    aview SEGS (w_H W1) (ms_mem ms3) x = aview SEGS (w_H W1) (ms_mem ms2) x).
  { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 x Hx).
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HR4 : dregs_top RG cx (ms_regs ms3)).
  { unfold dregs_top. split; [unfold spZ; rewrite P2, Uspa; exact Hsp|].
    rewrite USAa in P25, P26, P27.
    rewrite P3, P4, P22, P25, P27, P26, P18, P9, P8, P21, P23, P24.
    rewrite (OLDa 3%nat ltac:(lia)), (OLDa 4%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)),
      (OLDa 9%nat ltac:(lia)), (OLDa 8%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)),
      (OLDa 35%nat ltac:(lia)).
    rewrite (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 18%nat 18%bv eq_refl),
      (EE 9%nat 9%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 21%nat 21%bv eq_refl), E34, E35.
    rewrite R3, R4, R22, R18, R9, R8, R21.
    repeat split; reflexivity. }
  assert (E33a : ew Ea 33 = Z_to_bv 64 (re_skip e1)) by (rewrite (OLDa 33%nat ltac:(lia)); exact E33).
  apply (FIN (ms_regs ms3) (ms_mem ms3) _ NN (re_skip e1) HJ2 HR4).
  + intros x Hx N1 N2 N3 N4. rewrite (K3 x Hx N1 N2). exact (KM2 x Hx N1 N2 N3 N4).
  + intros x Hx. exact (apresent_grows _ _ _ _ HG3 (PM2 x Hx)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 24 8%N (SOff 25 0) NN RG2 USAa (or_introl eq_refl)
      (den_atom0 Ea 25 NN E25 ltac:(lia)) ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 8 4%N (SOff 33 0) (re_skip e1) RG1 USAa (or_introl eq_refl)
      (den_atom0 Ea 33 _ E33a ltac:(lia)) ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
  + intros i Hi.
    assert (NB : ~ (SA <= re_buf e1 + i < SA + 56)) by (unfold rs_hide in HTB; clear - Hi HTB HGSA HSAG HNN K8; lia).
    rewrite (K3 (re_buf e1 + i) ltac:(lia) ltac:(lia) ltac:(lia)). exact (VB2 i Hi).
  + unfold rs_hide. left. split; [exact Hc | split; reflexivity].
- rewrite branch_ltu_U, (U_atom Ea 25 NN E25), (U_lit Ea 6001) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 RBspan A_dr_top.
  { apply awr_ok_x_cons; [intros x Hx; cbn [rs_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    all: (intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite USAa in Hx;
      left; (split; [|lia]); right; left; split;
      [ unfold dFP, dr_fp, AENT; apply inFP_cons; left; change (dxSA cx) with SA; lia
      | exists (dxG cx), 896; split; [exact HGin1 | rewrite RQ; lia] ]). }
  rename ms into ms3.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem ms2)) _ |- _ => rename H into HG3 end.
  rename HF into HF3, HFr into HFr3.
  assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (SA + 8 <= x < SA + 12) -> ~ (SA + 24 <= x < SA + 32) ->
    aview SEGS (w_H W1) (ms_mem ms3) x = aview SEGS (w_H W1) (ms_mem ms2) x).
  { intros x Hx N1 N2. apply (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 x Hx).
    intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa, ?USAa in Hr; lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HR4 : dregs_top RG cx (ms_regs ms3)).
  { unfold dregs_top. split; [unfold spZ; rewrite P2, Uspa; exact Hsp|].
    rewrite USAa in P25, P26, P27.
    rewrite P3, P4, P22, P25, P27, P26, P18, P9, P8, P21, P23, P24.
    rewrite (OLDa 3%nat ltac:(lia)), (OLDa 4%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)),
      (OLDa 9%nat ltac:(lia)), (OLDa 8%nat ltac:(lia)), (OLDa 21%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)),
      (OLDa 35%nat ltac:(lia)).
    rewrite (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 18%nat 18%bv eq_refl),
      (EE 9%nat 9%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 21%nat 21%bv eq_refl), E34, E35.
    rewrite R3, R4, R22, R18, R9, R8, R21.
    repeat split; reflexivity. }
  apply (FIN (ms_regs ms3) (ms_mem ms3) _ 0 1 HJ2 HR4).
  + intros x Hx N1 N2 N3 N4. rewrite (K3 x Hx N1 N2). exact (KM2 x Hx N1 N2 N3 N4).
  + intros x Hx. exact (apresent_grows _ _ _ _ HG3 (PM2 x Hx)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 24 8%N (SLit 0) 0 RG2 USAa (or_introl eq_refl)
      eq_refl ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)).
  + exact (field_of_region Ea _ 32 SA _ _ _ _ _ 8 4%N (SLit 1) 1 RG1 USAa (or_introl eq_refl)
      eq_refl ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
  + intros i Hi.
    assert (NB : ~ (SA <= re_buf e1 + i < SA + 56)) by (unfold rs_hide in HTB; clear - Hi HTB HGSA HSAG HNN K8; lia).
    rewrite (K3 (re_buf e1 + i) ltac:(lia) ltac:(lia) ltac:(lia)). exact (VB2 i Hi).
  + unfold rs_hide. right. split; [exact Hc | split; reflexivity].
Qed.

End wR.

(* ---- the strict pieces: each is its R twin at R := @wle SEGS ---- *)
Theorem dr_rest_x : dr_rest_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_rest_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

End cx.
End b.
End a.
