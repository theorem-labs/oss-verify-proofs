(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the HEAD HALF of the image-B (fuzz_reply.asan-ubsan) TOP segment of
   fuzz_reply's drain and the composed TOP.  TOP (lib/B/W_drain_cx.v dr_top_stmt, DI 0x833c0 -> DI / DEND / DRB 0)
   is split at B's slot-found point 0x83524 (lib/B/W_drain_topb_cx.v A_dr_slot, a Theorem Labs lane, FROZEN):
     head  DI 0x833c0 -> DT2 0x83524 at the grown state dgrow s1: the round's growth (cap - used < 4096 tested
           as `(cap - used) >> 12 != 0` at 0x833e4; realloc #1 at 0x83410 through arealloc_cf_rule, whose forced
           success refutes the failure arm `beqz a0 -> 0x83fa8`), then source_of's scan over g_s 0x83498 ..
           0x834cc, which finds slot j at the `beq a1,a4` of 0x834c0 (the not-found exit 0x834d0 is refuted from
           DMEM's asrc_at at dHA (open = 1, fd = hs_fd) with DSAME / DBASE's hs_fd = re_fd, and aothers_at for the
           slots before j);
     tail  DT2 -> DI (EINTR) / DEND / DRB 0, a Theorem Labs lane's dr_toptail_stmt.
   0x83524 is reached only from that beq (0x83520 is `j 0x83574`), and between 0x833c0 and 0x83524 the code writes
   only s3, s7, a0-a6 and (at realloc) ra, so DI's dregs_top holds at the seam unchanged.
   dr_top_of composes the two halves: the tail's EINTR continuation at dclr sg is dr_top_stmt's at
   dclr (dgrow s1), because ds_eintr (dgrow s1) reduces to ds_eintr s1. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx W_drain_topb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Definition DBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition dt_shA (m : nat) (c : Z) : cval :=
  CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 35 0)).
#[local] Notation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 35 0)).
#[local] Notation dt_gv c := (SAlu ALU_SRL (SOff 8 c) (SLit 3)).
#[local] Notation BxT := (SOff 35 0).

Ltac dt_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E (setpc ?ss ?pc) (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E (setpc ss pc) ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs (setpc ss pc)) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Lemma dt_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma dt_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma dt_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof.
intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma dt_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite (IH (Z.shiftr z 8) k d ltac:(lia)), Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma dt_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0)))
  by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, dt_nth_zle by exact Hk. rewrite dt_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma dt_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma dt_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> abyte_kept W m W' m' x) ->
garr8 SEGS (arm W' m') a l.
Proof. intros W m W' m' a l H HK. exact (akept_garr8 W m W' m' a l HK H). Qed.
Lemma dt_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat)
  by (rewrite dt_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite dt_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma dt_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma dt_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac dt_len := rewrite ?length_app, ?dt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].
Lemma dt_entry_used : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_used e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 24) 8 (re_used e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 4 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_used e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.
Lemma dt_entry_cap : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_cap e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 32) 8 (re_cap e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 3 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_cap e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.
Lemma dt_den_reg : forall E (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma dt_U_gv : forall E v c, ew E 8 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (dt_gv c) = (v + c) / 8.
Proof.
intros E v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 8 v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma dt_U_sh : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 35 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (dt_sh m c) = shadow_addr (v + c).
Proof.
intros E m v c Hn H35 Hv Hc. unfold shadow_addr. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8))
  by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (U_atom E 35 SHADOW_OFF H35) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.
Lemma dt_den_sh : forall E m v c, ew E m = Z_to_bv 64 v -> ew E 35 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> sv_denot E (dt_sh m c) = w64 (shadow_addr (v + c)).
Proof.
intros E m v c Hn H35 Hv Hc. rewrite denot_lit_U. unfold w64. f_equal.
exact (dt_U_sh E m v c Hn H35 Hv Hc).
Qed.
Lemma dt_den_gv : forall E v c, ew E 8 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (dt_gv c) = w64 ((v + c) / 8).
Proof.
intros E v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. exact (dt_U_gv E v c Hn Hv Hc).
Qed.
Lemma dt_U_room : forall E cap used,
bv_unsigned (ew E 33) = cap -> bv_unsigned (ew E 34) = used -> 0 <= used <= cap -> cap <= 16384 ->
U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) = cap - used.
Proof.
intros E cap used H33 H34 Hu Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, U_SLit, H33, H34, !Z.add_0_r.
rewrite (zcanon_id used), (zcanon_id cap) by (unfold M64; lia).
change (zcanon (-1)) with (M64 - 1).
replace (zcanon (used * (M64 - 1))) with (zcanon (- used)).
2:{ unfold zcanon. replace (used * (M64 - 1)) with (- used + used * M64) by lia.
    symmetry. apply Z_mod_plus_full. }
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (cap + - used) with (cap - used) by lia.
apply Z.mod_small. lia.
Qed.
Lemma dt_bnez_room : forall E cap used,
bv_unsigned (ew E 33) = cap -> bv_unsigned (ew E 34) = used -> 0 <= used <= cap -> cap <= 16384 ->
branch_taken BC_NE
  (sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) (SLit 12)))
  (sv_denot E (SLit 0)) = (4096 <=? cap - used).
Proof.
intros E cap used H33 H34 Hu Hc. rewrite branch_ne_U.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (dt_U_room E cap used H33 H34 Hu Hc), U_SLit, (zcanon_id 12) by (unfold M64; lia).
change (Z.land 12 63) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
rewrite (zcanon_id ((cap - used) / 4096))
  by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite U_lit by lia.
destruct (Z.leb_spec 4096 (cap - used)) as [Hd|Hd].
- replace ((cap - used) / 4096 =? 0) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. assert (0 < (cap - used) / 4096) by (apply Z.div_str_pos; lia). lia.
- replace ((cap - used) / 4096 =? 0) with true; [reflexivity|].
  symmetry. apply Z.eqb_eq. apply Z.div_small. lia.
Qed.
Lemma dt_shent_sub : forall ly S (W : world SEGS) mem md E (m : nat) p n q lo hi,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m p n q lo hi HAR Hin HB Hm H1 H2 H3.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma dt_aentry_blks_in : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W m e (_ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hkeys) b Hb.
unfold aentry_blks in Hb.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
  + rewrite in_map_iff in Hb. destruct Hb as (k & <- & Hk).
    exact (proj1 (proj1 (Forall_forall _ _) Hkeys k Hk)).
  + destruct Hb as [<-|Hb].
    * destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
    * rewrite in_map_iff in Hb. destruct Hb as (k & <- & Hk).
      exact (proj1 (proj1 (Forall_forall _ _) Hkeys k Hk)).
- destruct Hb as [<-|Hb].
  + destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [app] in Hb.
    * rewrite in_map_iff in Hb. destruct Hb as (k & <- & Hk).
      exact (proj1 (proj1 (Forall_forall _ _) Hkeys k Hk)).
    * destruct Hb as [<-|Hb].
      -- destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
      -- rewrite in_map_iff in Hb. destruct Hb as (k & <- & Hk).
         exact (proj1 (proj1 (Forall_forall _ _) Hkeys k Hk)).
Qed.
Lemma dt_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [app] in Hb.
- rewrite in_map_iff in Hb. destruct Hb as (r & <- & Hr).
  exact (proj1 (proj1 (Forall_forall _ _) Hrecs r Hr)).
- destruct Hb as [<-|Hb].
  + destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
  + rewrite in_map_iff in Hb. destruct Hb as (r & <- & Hr).
    exact (proj1 (proj1 (Forall_forall _ _) Hrecs r Hr)).
Qed.
Lemma dt_asrc_blks_in : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W m HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpart & _ & _ & _ & Hexp & Hheld & _).
unfold asrc_blks in Hb. destruct Hb as [<-|Hb]; [exact Hpart|].
apply in_app_or in Hb. destruct Hb as [Hb|Hb];
  [exact (dt_alist_blks_in ly S W m (HA + 16) (hs_pending h) false Hpend b Hb)|].
apply in_app_or in Hb. destruct Hb as [Hb|Hb];
  [exact (dt_alist_blks_in ly S W m (HA + 64) (hs_expected h) true Hexp b Hb)
  |exact (dt_alist_blks_in ly S W m (HA + 80) (hs_held h) true Hheld b Hb)].
Qed.
Lemma dt_aout_blks_in : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W m c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn in Hb; [destruct Hb|].
destruct Hb as [<-|[]].
destruct Hblk as [(Hc & _)|(_ & _ & Hin & _)]; [lia | exact Hin].
Qed.
Lemma dt_aentry_okx_kept : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e,
aentry_okx B ly S W m e -> akept W m W' m' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) -> aentry_okx B ly' S' W' m' e.
Proof.
intros ly S W m ly' S' W' m' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.
Lemma dt_DMEM_kept : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 &
    A17 & A18 & A19 & A20 & A21 & A22 & A23 & ASV).
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (ASV i Hi) ]. }
split; [exact (dt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => Hkept x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (dt_aentry_okx_kept ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (dt_aentry_blks_in ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (dt_asrc_blks_in ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (dt_aout_blks_in ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.


Definition A_dr_mid : Z := AF_fr_drain + 0x1c0.

Definition DT1 (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_mid) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

Definition dt_nogrow_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition dt_grow_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition dt_scan_stmt : Prop :=
forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT1 cx sg D W1 c1 ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition dr_tophead_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
(forall W2 c2, DT2 B MT MMAX RG cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Theorem dr_tophead_of : dt_nogrow_stmt -> dt_grow_stmt -> dt_scan_stmt -> dr_tophead_stmt.
Proof.
intros NG GR SC cx s1 D W1 c1 HB HDI K.
assert (KT1 : forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx))
  by (intros W2 c2 H2; exact (SC cx (dgrow s1) D W2 c2 HB H2 K)).
destruct (Z_le_gt_dec 4096 (drain_b_c.ds_cap s1 - ulen s1)) as [Hge|Hlt].
- exact (NG cx s1 D W1 c1 HB HDI Hge KT1).
- exact (GR cx s1 D W1 c1 HB HDI ltac:(lia) KT1).
Qed.


Theorem dr_top_of : dr_tophead_stmt -> dr_toptail_stmt B MT MMAX RG -> dr_top_stmt B MT MMAX RG.
Proof.
intros HEAD TAIL cx s1 D W1 c1 HB HI KE KD KR.
apply (HEAD cx s1 D W1 c1 HB HI). intros W2 c2 H2.
exact (TAIL cx (dgrow s1) D W2 c2 HB H2 KE KD KR).
Qed.
Definition dt_HEAPF : afact := mkAF 4096 140737479966720 0.
Definition dt_IMGF : afact := mkAF 0x10000 IMG_TOP 3.
Definition dt_regs_top : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
  21%bv (SOff 32 0)) 24%bv (SOff 32 8)) 20%bv (SOff 32 16)) 22%bv (SOff 32 24))
  27%bv (SOff 32 32)) 9%bv (dt_gv 0)) 18%bv (dt_gv 4)) 26%bv (SLit 384).
Definition dt_ng_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 0 0
  [ YP09.mkChunk 216 (dt_shA 32 32); YP09.mkChunk 232 (dt_shA 32 24) ].
Definition dt_ng_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition dt_ng_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF SB SB 0); (8%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0) ] [] [].
Definition ss_ng : sstate := mkSS A_dr_top dt_regs_top [ dt_ng_frame; dt_ng_sa ] None dt_ng_facts.
Definition SHng : list shent := [ mkSHE 32 0 56 ].
Definition dt_ng_extra (SA cap used : Z) : list word := map (Z_to_bv 64) [SA; cap; used; SHADOW_OFF].
Definition A_dr_scan : Z := AF_fr_drain + 0x220.

Definition DSC (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_scan) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
getr regs1 14 = w64 (re_fd e1) /\ getr regs1 12 = w64 (96 * Z.of_nat i) /\
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat i) /\
(i <= dxj cx)%nat /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

Definition dt_scan_entry_stmt : Prop :=
forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT1 cx sg D W1 c1 ->
(forall W2 c2, DSC cx sg D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition dt_scan_step_stmt : Prop :=
forall cx sg D i W1 c1,
DBASE B MT MMAX RG cx -> DSC cx sg D i W1 c1 ->
(forall W2 c2, DSC cx sg D (S i) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Lemma dt_DSC_le : forall cx sg D i W1 c1, DSC cx sg D i W1 c1 -> (i <= dxj cx)%nat.
Proof.
intros cx sg D i W1 c1
  (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
   _ & _ & _ & _ & _ & _ & _ & Hle & _).
exact Hle.
Qed.

Lemma dt_scan_loop : forall n cx sg D i W1 c1,
(4 - i <= n)%nat -> dt_scan_step_stmt -> DBASE B MT MMAX RG cx -> DSC cx sg D i W1 c1 ->
(forall W2 c2, DT2 B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
induction n as [|n IH]; intros cx sg D i W1 c1 Hn STEP HB HD K.
- assert (Hi : (i <= dxj cx)%nat) by exact (dt_DSC_le cx sg D i W1 c1 HD).
  assert (Hj : (dxj cx < 4)%nat)
    by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _); exact Hj).
  exfalso. clear - Hn Hi Hj. lia.
- apply (STEP cx sg D i W1 c1 HB HD); [|exact K].
  intros W2 c2 H2. apply (IH cx sg D (S i) W2 c2); [|exact STEP|exact HB|exact H2|exact K].
  assert (Hi : (S i <= dxj cx)%nat) by exact (dt_DSC_le cx sg D (S i) W2 c2 H2).
  assert (Hj : (dxj cx < 4)%nat)
    by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _); exact Hj).
  clear - Hn Hi Hj. lia.
Qed.

Theorem dt_scan_of : dt_scan_entry_stmt -> dt_scan_step_stmt -> dt_scan_stmt.
Proof.
intros ENTRY STEP cx sg D W1 c1 HB HD1 K.
apply (ENTRY cx sg D W1 c1 HB HD1). intros W2 c2 H2.
exact (dt_scan_loop 4 cx sg D 0 W2 c2 ltac:(lia) STEP HB H2 K).
Qed.

Definition dev_ok (ev : RelayRunT.rev YO0i.sptr) : Prop :=
match ev with
| RelayRunT.RMalloc n => 0 <= n
| RelayRunT.RFree n _ => 0 <= n
| RelayRunT.RRealloc _ n _ => 0 <= n
end.

Lemma dt_meters_nonneg : forall (tr : list (RelayRunT.rev YO0i.sptr)), Forall dev_ok tr -> 0 <= tr_alloc tr /\ 0 <= tr_cost MT tr.
Proof.
pose proof (mo_free_nonneg MT MTL) as HF0.
induction tr as [|ev tr IH]; intros HF; [unfold tr_alloc, tr_cost; cbn [fold_right]; lia|].
apply Forall_cons_iff in HF as [Hev HF'].
destruct (IH HF') as [Ha Hc].
unfold tr_alloc, tr_cost in Ha, Hc |- *. cbn [fold_right].
destruct ev as [n|n a|k n a]; cbn [dev_ok] in Hev.
- pose proof (mo_malloc_nonneg MT MTL n Hev). split; lia.
- split; lia.
- pose proof (mo_malloc_nonneg MT MTL n Hev). split; lia.
Qed.

Lemma dt_app_ok : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)), Forall dev_ok t1 -> Forall dev_ok t2 -> Forall dev_ok (t1 ++ t2).
Proof. intros t1 t2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma dt_grow_ok : forall cap used j b, 0 <= cap ->
Forall dev_ok (fst (drain_b_c.grow_tr cap used j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr cap used j b)).
Proof.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); cbn [fst snd]; [|split; [apply Forall_nil | exact Hc]].
destruct (Z.eqb_spec cap 0) as [Hq|Hq]; cbn [fst snd];
  (split; [apply Forall_cons; [cbn [dev_ok]; lia | apply Forall_nil] | lia]).
Qed.

Lemma dt_sl_ok : forall fuel mx no cap rem j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
Forall dev_ok (fst (send_line_b_c.sl_run fuel mx no cap rem j o)) /\
0 <= fst (snd (send_line_b_c.sl_run fuel mx no cap rem j o)).
Proof.
induction fuel as [|f IH]; intros mx no cap rem j o Hmx Hno Hcap;
  [cbn [send_line_b_c.sl_run fst snd]; split; [apply Forall_nil | exact Hcap]|].
cbn [send_line_b_c.sl_run].
destruct (rem <=? 0) eqn:Hrem; [cbn [fst snd]; split; [apply Forall_nil | exact Hcap]|].
apply Z.leb_gt in Hrem.
set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
assert (Hn : 0 <= n) by (unfold n; destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + n) eqn:Hlt.
- destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) Hmx ltac:(lia) ltac:(lia))
    as [Hok Hc2].
  cbn [fst snd]. split; [|exact Hc2].
  apply Forall_cons; [destruct (cap =? 0); cbn [dev_ok]; lia | exact Hok].
- exact (IH mx (no + n) cap (rem - n) j o Hmx ltac:(lia) Hcap).
Qed.

Lemma dt_sline_ok : forall live mx no cap len j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
Forall dev_ok (send_line_b_c.send_line_tr live mx no cap len j o) /\
0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
intros live mx no cap len j o Hmx Hno Hcap.
unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|split; [apply Forall_nil | exact Hcap]].
split; [exact (proj1 (dt_sl_ok (Z.to_nat len) mx no cap len j o Hmx Hno Hcap))
       |exact (proj2 (dt_sl_ok (Z.to_nat len) mx no cap len 0 RelayRunF.adr0 Hmx Hno Hcap))].
Qed.

Lemma dt_seen_ok : forall H ka l j ha ks, 0 <= ka ->
Forall dev_ok (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) /\
0 <= snd (fst (drain_b_c.seen_tr H ka l j ha ks)).
Proof.
intros H ka l j ha ks Hka. unfold drain_b_c.seen_tr.
destruct (gesture l) as [[kd x]|]; [|cbn [fst snd]; split; [apply Forall_nil | exact Hka]].
destruct kd.
- destruct (index_of x H); cbn [fst snd]; [split; [apply Forall_nil | exact Hka]|].
  split.
  + apply Forall_cons; [destruct (ka =? 0); cbn [dev_ok]; lia|].
    apply Forall_cons; [cbn [dev_ok]; lia | apply Forall_nil].
  + lia.
- destruct (index_of x H); cbn [fst snd]; [|split; [apply Forall_nil | exact Hka]].
  split; [apply Forall_cons; [cbn [dev_ok]; lia | apply Forall_nil] | exact Hka].
Qed.

Lemma dt_lines_ok : forall ls live mx no cap H ka j o ha ks, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= ka ->
Forall dev_ok (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
0 <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) /\
0 <= snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hmx Hno Hcap Hka;
  [cbn [drain_b_c.lines_run fst snd]; split; [apply Forall_nil | split; assumption]|].
cbn [drain_b_c.lines_run].
set (len := Z.of_nat (length l) + 1).
set (t1 := send_line_b_c.send_line_tr live mx no cap len j o).
set (sn := drain_b_c.seen_tr H ka l (j + RelayRunT.nret _ t1)%nat ha ks).
destruct (dt_sline_ok live mx no cap len j o Hmx Hno Hcap) as [Ht1 Hcap1]. fold t1 in Ht1.
destruct (dt_seen_ok H ka l (j + RelayRunT.nret _ t1)%nat ha ks Hka) as [Hsn Hka1]. fold sn in Hsn, Hka1.
destruct (IH live mx (no + len) (send_line_b_c.send_line_cap live mx no cap len) (seen_arr H l)
  (snd (fst sn)) (j + RelayRunT.nret _ t1 + RelayRunT.nret _ (fst (fst sn)))%nat
  (send_line_b_c.send_line_out live mx no cap len j o) (fst (snd sn)) (snd (snd sn))
  Hmx ltac:(unfold len; lia) Hcap1 Hka1) as [Hp1 [Hp2 Hp3]].
cbn [fst snd]. split; [|split; [exact Hp2 | exact Hp3]].
apply dt_app_ok; [exact Ht1 | apply dt_app_ok; [exact Hsn | exact Hp1]].
Qed.

Lemma dt_pushes_ok : forall ls n cap j v rs, 0 <= cap ->
Forall dev_ok (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
induction ls as [|l r IH]; intros n cap j v rs Hcap;
  [cbn [drain_b_c.pushes_run fst snd]; split; [apply Forall_nil | exact Hcap]|].
cbn [drain_b_c.pushes_run].
assert (Hpc : 0 <= drain_b_c.push_cap n cap)
  by (unfold drain_b_c.push_cap; destruct (n =? cap); [destruct (cap =? 0); lia | exact Hcap]).
destruct (IH (n + 1) (drain_b_c.push_cap n cap)
  (j + RelayRunT.nret _ (ListTr.list_push_tra v n cap (Z.of_nat (length l))))%nat
  (if n =? cap then RelayRunT.Ret j else v)
  (rs ++ [RelayRunT.Ret (Nat.pred (j + RelayRunT.nret _ (ListTr.list_push_tra v n cap (Z.of_nat (length l)))))])
  Hpc) as [Hp1 Hp2].
cbn [fst snd]. split; [|exact Hp2].
apply dt_app_ok; [|exact Hp1].
unfold ListTr.list_push_tra. apply dt_app_ok.
- destruct (n =? cap); [|apply Forall_nil].
  destruct (cap =? 0); apply Forall_cons; solve [cbn [dev_ok]; lia | apply Forall_nil].
- apply Forall_cons; [cbn [dev_ok]; lia | apply Forall_nil].
Qed.

Definition dinv (s : drain_b_c.dstate) : Prop :=
0 <= drain_b_c.ds_cap s /\ 0 <= drain_b_c.ds_ka s /\ 0 <= drain_b_c.ds_ecap s /\
0 <= drain_b_c.ds_ocap s /\ 0 <= drain_b_c.ds_no s.

Lemma dt_run_ok : forall fuel live mx s j a, 0 <= mx -> dinv s ->
Forall dev_ok (fst (drain_b_c.drain_run fuel live mx s j a)).
Proof.
induction fuel as [|f IH]; intros live mx s j a Hmx HI; [cbn [drain_b_c.drain_run fst]; apply Forall_nil|].
pose proof HI as (Hcap & Hka & Hecap & Hocap & Hno).
cbn [drain_b_c.drain_run].
pose proof (dt_grow_ok (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hcap)
  as [Hgok Hgcap].
set (g := drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j
  (drain_b_c.da_buf a)) in *.
destruct (drain_b_c.ds_eintr s).
{ cbn [fst snd]. apply dt_app_ok; [exact Hgok|].
  apply IH; [exact Hmx|]. unfold dinv; cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_ecap
    drain_b_c.ds_ocap drain_b_c.ds_no]. repeat split; assumption. }
destruct (drain_b_c.ds_pend s) as [|r0 rs]; [cbn [fst snd]; exact Hgok|].
match goal with |- context [if (Z.min ?x ?y <=? 0) then _ else _] => destruct (Z.min x y <=? 0) end;
  [cbn [fst snd]; exact Hgok|].
match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] eqn:Hch end.
match goal with |- context [drain_b_c.lines_run ?lv ?m ?n0 ?c0 ?H0 ?k0 rl ?j0 ?o0 ?h0 ?ks0] =>
  pose proof (dt_lines_ok rl lv m n0 c0 H0 k0 j0 o0 h0 ks0 Hmx Hno Hocap Hka) as (Hsl1 & Hsl2 & Hsl3);
  set (LR := drain_b_c.lines_run lv m n0 c0 H0 k0 rl j0 o0 h0 ks0) in *
end.
destruct (snd (fst LR)) as [[oc' H'] ka'] eqn:Hsl.
destruct (snd LR) as [[o' ha'] ks'] eqn:Hsl'.
match goal with |- context [drain_b_c.pushes_run ?n1 ?c1 ?ls1 ?j1 ?v1 ?rs1] =>
  pose proof (dt_pushes_ok ls1 n1 c1 j1 v1 rs1 Hecap) as (Hpu1 & Hpu2);
  set (PU := drain_b_c.pushes_run n1 c1 ls1 j1 v1 rs1) in *
end.
cbn [fst snd].
apply dt_app_ok; [exact Hgok|].
apply dt_app_ok; [exact Hpu1|].
apply dt_app_ok.
{ match goal with |- context [if ?w then ListTr.list_drop_tra _ _ else []] => destruct w end;
  [unfold ListTr.list_drop_tra; apply Forall_cons; [cbn [dev_ok]; lia | apply Forall_nil] | apply Forall_nil]. }
apply dt_app_ok; [exact Hsl1|].
apply IH; [exact Hmx|].
unfold dinv; cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_no].
cbn [fst snd] in Hsl2, Hsl3.
repeat split; [exact Hgcap | exact Hsl3 | exact Hpu2 | exact Hsl2 | lia].
Qed.

Lemma dt_later_meters : forall cx s2 jb2 a2 tl2,
0 <= dxmx cx -> dinv s2 -> dlater cx s2 jb2 a2 tl2 -> 0 <= tr_alloc tl2 /\ 0 <= tr_cost MT tl2.
Proof.
intros cx s2 jb2 a2 tl2 Hmx HI (fuel & _ & _ & Htl & _).
apply dt_meters_nonneg. rewrite <- Htl.
exact (dt_run_ok fuel (dlive cx) (dxmx cx) s2 jb2 a2 Hmx HI).
Qed.


Theorem dt_nogrow : dt_nogrow_stmt.
Proof.
intros cx s1 D W1 c1 HB HDI Hge K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (Heof & Hskipv & Hpad1 & Hpad2 & Hfdv & Hcapv & HUlen & Hucap & Hbufc & Hnheld & Hheldc &
  HND1 & HND2 & Hkeys).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384) by lia.
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen1 : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUlen).
assert (Hcappos : 0 < re_cap e1).
{ pose proof Hge as Hg'. rewrite <- Lcap, Hulen1 in Hg'.
  pose proof (Nat2Z.is_nonneg (length (re_U e1))). lia. }
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_ng_extra (dxSA cx) (re_cap e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_ng
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ng. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_ng_frame, dt_ng_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      pose proof HFR as (G8 & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G88 & G104 & G120 & G128 & G136 &
        G144 & G152 & G176 & G184 & G200 & G208 & G216 & G224 & G232 & G240 & Gsaved).
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact (dt_den_sh E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia); zside])
          | zside
          | exact G216 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh E 32 (dxSA cx) 24 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia); zside])
          | zside
          | exact G232 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_cap W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_ng_frame, dt_ng_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_ng_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUN BR HS SHOK DBspan.
- paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_mid.
  { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  rewrite wvb_collapse in HJ.
  assert (Hnw : forall x, ~ in_wrange E (ss_mem ss_ng) x).
  { intros x (r & Hin & Hr). cbv [ss_mem ss_ng dt_ng_frame dt_ng_sa] in Hin.
    destruct Hin as [Hq|[Hq|[]]]; subst r;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a.
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (Hnw _))).
    exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (Hnw _))). }
  assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22.
  dt_reg HS (24%bv : bv 5) X24. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  apply K. rewrite (dgrow_id s1 Hge). unfold DT1.
  eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
    split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
    split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
    split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
    split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
    split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
           |rewrite X26; exact (eq_trans (eq_sym R26') R26)]. }
  split; [exact (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split; [apply Hband; lia|].
  split; [exact HLINK|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hge|].
  split; [exact Hlater | exact Hbud].
- rewrite (dt_bnez_room E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_gt in Hc.
  pose proof Hge as Hg2. rewrite <- Lcap, Hulen1 in Hg2. lia.
Qed.

(* ==== GROW (dt_grow): the helpers, ported from lib/A/W_drain_top.v on a working branch 752503c26ca
   (lines 180-190, 241-246, 719-1077, 1096-1601); image-free unless marked [B]. ==== *)

Lemma dt_entry_buf : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 16) 8 (re_buf e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 5 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_buf e) Hv) in H.
apply (dt_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H). dt_len. lia.
Qed.

Lemma dt_nowr_lem : forall E (rs : smem),
forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true -> forall x, ~ in_wrange E rs x.
Proof.
intros E rs HF x (r & Hin & Hr).
rewrite forallb_forall in HF. pose proof (HF r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

Lemma dt_garr8_keptv : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H KL. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (KL x Hx).
Qed.

Lemma dt_gx_open : forall G STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k,
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k.
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.
Lemma dt_gx_close : forall G STK sp0 FP ly S W0 mem md own ly2 S2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal SEGS B STK sp0 FP ly S W0 memS md own ly2 S2 W2 mem2 md2 k2 ->
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

(* No live block is listed twice: two copies would have to be disjoint from themselves. *)
Lemma dt_no_dup_block : forall ly S (W : world SEGS) mem md x l,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: x :: l) -> 0 <= snd x -> False.
Proof.
intros ly S W mem md x l HAR HP Hn.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x l HAR HP) as Hd.
pose proof (req_size_pos (snd x) Hn) as (Hr & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* A byte of a block of the entry's own footprint list is a byte the walk declared. *)
Lemma dt_inFP_of_blocks : forall bl p n i SA,
In (p, n) bl -> 0 <= i < req_size n -> inFP ((SA, SA + AENT) :: ablocks_fp bl) (p + i).
Proof.
intros bl p n i SA Hin Hi. exists (p, p + req_size n). split; [right|cbn [fst snd]; lia].
exact (in_map (fun b => (fst b, fst b + req_size (snd b))) bl (p, n) Hin).
Qed.

(* The buffer the round hands to realloc: if it was already a block when drain was entered, it is one of the
   blocks the walk declared.  It cannot be the relay's table (its requested size is not a capacity), and it
   cannot be one of the blocks drain found live and left alone (dxrest): the entry's buffer is a block at the
   cut too, so the cut's block list would hold it twice. *)
Lemma dt_buf_fp : forall cx ly1 S1 (W1 : world SEGS) m1 md1 bl p n,
AR SEGS B ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: bl ++ dxrest cx) -> In (p, n) bl ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++
     dxrest cx) ->
In (p, n) (ablocks B (dxly cx) (dxS cx)) -> 0 <= n -> n <> ATABLE ->
forall i, 0 <= i < req_size n -> inFP (dFP cx) (p + i).
Proof.
intros cx ly1 S1 W1 m1 md1 bl p n HAR HPc Hbl HP0 Hin0 Hn Hnt i Hi.
unfold dFP, dr_fp.
assert (Hin : In (p, n) ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx)) by (eapply Permutation_in; [exact HP0 | exact Hin0]).
destruct Hin as [Heq | Hin]; [injection Heq as _ Heq; congruence|].
apply in_app_or in Hin as [Hin | Hin]; [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_introl Hin)) Hi)|].
apply in_app_or in Hin as [Hin | Hin];
  [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hin)))) Hi)|].
apply in_app_or in Hin as [Hin | Hrest];
  [exact (dt_inFP_of_blocks _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hin)))) Hi)|].
exfalso.
destruct (in_split _ _ Hbl) as (b1 & b2 & Eb).
destruct (in_split _ _ Hrest) as (d1 & d2 & Ed).
apply (dt_no_dup_block ly1 S1 W1 m1 md1 (p, n) ((dxG cx, ATABLE) :: b1 ++ b2 ++ d1 ++ d2)); [exact HAR | | exact Hn].
eapply Permutation_trans; [exact HPc|].
rewrite Eb, Ed, <- !app_assoc.
apply Permutation_sym.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: b1) (l2 := b2 ++ d1 ++ (p, n) :: d2).
cbn [app]. rewrite !app_assoc.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: (b1 ++ b2) ++ d1) (l2 := d2).
apply Permutation_refl.
Qed.

(* Twice the old capacity, as the slli at 0x83230 leaves it. *)
Lemma dt_den_sll : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v -> 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 1)) = w64 (v * 2).
Proof.
intros E n v Hn Hv Hv2. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn ltac:(lia)), U_SLit.
rewrite (zcanon_id 1) by (unfold M64; lia). change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
apply zcanon_id. unfold M64. lia.
Qed.

(* The capacity test at 0x83224. *)
Lemma dt_bnez_atom : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_ne_U.
rewrite (U_atom E n v Hn ltac:(lia)), U_lit by lia.
destruct (Z.eqb_spec v 0) as [->|Hne]; reflexivity.
Qed.

(* The capacity the round asks for: 8192 from nothing, twice the old one otherwise (Prog/drain_b_c.v grow_tr). *)
Lemma dt_gcap_grow : forall cap used, used <= cap -> cap - used < 4096 ->
gcap cap used = (if cap =? 0 then 8192 else cap * 2).
Proof.
intros cap used Hu Hlt. unfold gcap, drain_b_c.grow_tr.
rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst snd]. reflexivity.
Qed.

(* The round's growth always leaves at least 4096 free: from nothing it takes 8192, and a buffer only grows
   when it has less than 4096 free, which for the splitter's 6000-byte partial can only be the 8192 one. *)
Lemma dt_grow_room : forall s1,
drain_b_c.ds_cap s1 - ulen s1 < 4096 -> 0 <= ulen s1 <= APARTIAL -> ulen s1 <= drain_b_c.ds_cap s1 ->
(drain_b_c.ds_cap s1 = 0 \/ drain_b_c.ds_cap s1 = 8192 \/ drain_b_c.ds_cap s1 = 16384) ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1).
Proof.
intros s1 Hlt Hu Huc Hc.
change (ulen (dgrow s1)) with (ulen s1).
change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) Huc Hlt).
unfold APARTIAL in Hu. destruct Hc as [Hq|[Hq|Hq]]; rewrite Hq; cbn [Z.eqb]; lia.
Qed.

(* What the walk may still spend, as the allocator rules ask for it (W_drain_gs.v gs_mo_ok_of). *)
Lemma dt_mo_ok_of : forall cx S1 spent tl c,
mo_ok MT (dxS cx) (dcost MT cx) -> dbud MT MMAX cx S1 spent tl ->
0 <= c -> c <= tr_cost MT tl -> mo_ok MT S1 c.
Proof.
intros cx S1 spent tl c Hok (Hle & Hsp & Hcost & _ & _) Hc0 Hc.
apply (mok_station MT (dxS cx) S1 (dcost MT cx) spent c MTL Hok Hle); lia.
Qed.

(* The three meters over an append, and what the growth's own request costs. *)
Lemma dt_tr_cost_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)), tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_alloc_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_max_nonneg : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof.
intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
cbn [fold_right]. destruct ev; lia.
Qed.
Lemma dt_tr_max_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)), tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (dt_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma dt_grow_ev : forall cap used j b, 0 <= cap -> used <= cap -> cap - used < 4096 ->
tr_max (fst (drain_b_c.grow_tr cap used j b)) = gcap cap used /\
tr_alloc (fst (drain_b_c.grow_tr cap used j b)) = gcap cap used /\
tr_cost MT (fst (drain_b_c.grow_tr cap used j b)) = mo_malloc MT (gcap cap used) + mo_free MT.
Proof.
intros cap used j b Hc0 Hu Hlt.
rewrite (dt_gcap_grow cap used Hu Hlt).
unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst snd].
destruct (cap =? 0); cbn [tr_max tr_alloc tr_cost fold_right];
  (split; [lia|]); (split; lia).
Qed.
(* C3: the growth's one request (malloc of the new capacity from nothing, else realloc of the old capacity cap to it)
   gets its live-bytes premise from the peak of the trace it opens, and moves the live bytes by gcap - cap, so the
   peak of what follows stays in room (W_tr_peak.v tr_peak_malloc / tr_peak_realloc). *)
Lemma dt_grow_pk : forall cap used j b (t : list (RelayRunT.rev YO0i.sptr)) bb, 0 <= cap -> used <= cap ->
cap - used < 4096 ->
bb + tr_peak (fst (drain_b_c.grow_tr cap used j b) ++ t) <= LIVE_MAX ->
bb + gcap cap used <= LIVE_MAX /\ bb - cap + gcap cap used + tr_peak t <= LIVE_MAX.
Proof.
intros cap used j b t bb Hc0 Hu Hlt H.
pose proof (W_tr_peak.tr_peak_nonneg t) as Ht.
rewrite (dt_gcap_grow cap used Hu Hlt).
unfold drain_b_c.grow_tr in H. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt) in H. cbn [fst app] in H.
destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota in H |- *;
  [rewrite W_tr_peak.tr_peak_malloc in H | rewrite W_tr_peak.tr_peak_realloc in H]; lia.
Qed.

(* The round's growth is the first thing the rest of the walk owes the allocator: one request for the new
   capacity, then the rounds of the grown state (W_drain_model.v drun_grow). *)
Lemma dt_grow_tr : forall cx s1 jb a tl,
dlater cx s1 jb a tl -> 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
exists tl2,
  tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf a)) ++ tl2 /\
  dlater cx (dgrow s1)
    (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf a))))
    (agrow s1 jb a) tl2.
Proof.
intros cx s1 jb a tl (fuel & Hneed & Hwf & Htr & Hfin) Hroom.
destruct fuel as [|f]; [unfold dneed in Hneed; lia|].
rewrite (drun_grow f (dlive cx) (dxmx cx) s1 jb a Hroom) in Htr, Hfin. cbn [fst snd] in Htr, Hfin.
eexists. split; [exact (eq_sym Htr)|].
exists (S f). split; [unfold dneed, pstream; cbn [dgrow drain_b_c.ds_pend drain_b_c.ds_off
  drain_b_c.ds_eintr]; unfold dneed, pstream in Hneed; lia|].
split; [|split; [reflexivity | exact Hfin]].
unfold dwf in Hwf |- *. cbn [dgrow drain_b_c.ds_off drain_b_c.ds_pend]. exact Hwf.
Qed.

Ltac dt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* the `beqz a0` at 0x8324c *)
Lemma dt_beqz_atom : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_eq_U.
rewrite (U_atom E n v Hn Hv), U_lit by lia. reflexivity.
Qed.

(* ---- Byte transport across the call and the two stores (the form of W_gsfree_scratch.v's gm_ lemmas). ---- *)
Lemma dt_in_zr_dec : forall x r, {in_zr x r} + {~ in_zr x r}.
Proof.
intros x r. unfold in_zr. destruct (Z_le_gt_dec (fst r) x); destruct (Z_lt_ge_dec x (fst r + snd r));
[left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma dt_bk_trans : forall (W0 : world SEGS) m0 (W1 : world SEGS) m1 (W2 : world SEGS) m2 x,
abyte_kept W0 m0 W1 m1 x -> abyte_kept W1 m1 W2 m2 x -> abyte_kept W0 m0 W2 m2 x.
Proof.
intros W0 m0 W1 m1 W2 m2 x [V1 P1] [V2 P2]. split; [rewrite V2; exact V1 | intros H; exact (P2 (P1 H))].
Qed.

(* a byte stays writable across two worlds when its presence is kept *)
Lemma dt_wr_kept2 : forall (H H2 : word -> bool) (m m2 : word -> option byte) a,
(apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; destruct (H2 (Z_to_bv 64 a)) eqn:EH2; intros Hw.
- exact Hw.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hc _]. rewrite Hc in EH2. discriminate.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* a byte of a writable image segment whose view is defined is writable *)
Lemma dt_img_wr : forall (W : world SEGS) m a,
in_img SEGS a -> ~ in_rom SEGS a -> aview SEGS (w_H W) m a <> None -> writable_at SEGS (arm W m) a.
Proof.
intros W m a Hi Hr Hv.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (Hfn : find_segment SEGS a 1 <> None) by (apply find_segment_img; exact Hi).
destruct (find_segment SEGS a 1) as [sg|] eqn:Hf; [|exfalso; exact (Hfn eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
assert (Hw : seg_writable sg = true).
{ destruct (seg_writable sg) eqn:E; [reflexivity|]. exfalso. apply Hr. exists sg.
  split; [exact Hin|]. split; [exact E|]. lia. }
revert Hv. unfold aview, writable_at, arm, mbyte, wview, mrestrict, seg_rom, memory_read.
rewrite HA. rewrite ?Ha.
destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; discriminate|].
change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta. rewrite Hw. cbv beta iota.
destruct (seg_readable sg); [|intros H; exfalso; apply H; reflexivity].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at _ _); [intros _; discriminate | intros H; exfalso; apply H; reflexivity].
Qed.

(* two blocks at distinct places of a permutation of the live blocks are apart *)
Lemma dt_sep_head : forall ly S (W : world SEGS) m md x L y,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma dt_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.

(* every byte a list's predicate reads is in its struct or in one of its blocks *)
Lemma dt_list_fp : forall ly S (W : world SEGS) m LA l lines, alist_at B ly S W m LA l lines ->
forall r x, In r (alist_fp LA l) -> fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r x Hr Hx. pose proof HL as (_ & _ & _ & _ & Hnc & H6 & _ & _ & H9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn in Hx; lia|]. right.
apply in_app_iff in Hr as [Hr|Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]].
  destruct H6 as [(Hc & _) | (Hc0 & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  exists (hl_v l, AREC * hl_cap l).
  split; [unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app, dt_concat_len in Hx. unfold req_size, AREC, hl_n in *.
  destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|]. lia.
- apply in_map_iff in Hr as (t & <- & Ht).
  exists (fst t, Z.of_nat (length (snd t)) + 1).
  split; [unfold alist_blks; apply in_or_app; right;
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Ht|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. unfold req_size.
  destruct (Z.of_nat (length (snd t)) + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.

(* every byte a source's predicate reads is in the struct source or in one of its blocks *)
Lemma dt_src_fp : forall ly S (W : world SEGS) m HA h, asrc_at B ly S W m HA h ->
forall r x, In r (asrc_fp HA h) -> fst r <= x < snd r ->
(HA <= x < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m HA h HS r x Hr Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. exact Hx.
- right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *. unfold bzs in Hx. rewrite length_map in Hx.
  assert (RQ : req_size APARTIAL = APARTIAL) by reflexivity. rewrite RQ. lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (dt_list_fp ly S W m (HA + 16) (hs_pending h) false Hpend r x Hr Hx) as [H | (b & Hb & Hbx)];
      [left; unfold ASRC; lia | right; exists b; split; [right; apply in_or_app; left; exact Hb | exact Hbx]].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (dt_list_fp ly S W m (HA + 64) (hs_expected h) true Hexp r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hbx]].
    * destruct (dt_list_fp ly S W m (HA + 80) (hs_held h) true Hheld r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbx]].
Qed.

(* every byte the output's predicate reads is a walk global, one of its three read-only cells, or g_out *)
Lemma dt_out_fp : forall cap out r x, In r (aout_fp B RG cap out) -> fst r <= x < snd r ->
inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x \/
(cap <> 0 /\ out <= x < out + cap).
Proof.
intros cap out r x Hr Hx. unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx;
try (left; unfold G_DR, G_SL, inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail);
try (right; left; unfold inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail).
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
right; right. split; [apply Z.eqb_neq in Hc0; exact Hc0 | exact Hx].
Qed.

(* [B] drain's frame slots, every one in [sp, sp + 352), across two worlds: 23 one-time slots and the 13 saves at
   248 .. 344 (lib/B/W_drain_cx.v dr_frame / dr_saved). *)
Lemma dt_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 &
  F19 & F20 & F21 & F22 & F23 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
unfold dr_saved in HS |- *. intros i Hi. specialize (HS i Hi). unfold DR_SAVE_OFF in *.
replace (dsp0 cx - DRAIN_FRAME + 248 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (248 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

Lemma dt_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
change (key_ptrs (k :: ks)) with (Mem.le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks).
rewrite length_app, Mem.length_le8, IH. cbn [length]. lia.
Qed.

Lemma dt_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.

Lemma dt_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite dt_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite dt_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite dt_le_byte1 by exact Hr. reflexivity.
Qed.

(* a byte run copied from one place to another (the realloc's copy of the old buffer) keeps its image *)
Lemma dt_garr8_shift : forall (W : world SEGS) m (W' : world SEGS) m' a a' l,
garr8 SEGS (arm W m) a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a' + i) = aview SEGS (w_H W) m (a + i)) ->
garr8 SEGS (arm W' m') a' l.
Proof.
intros W m W' m' a a' l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. specialize (Hv k Hk). rewrite <- Hv.
replace (Z.of_nat k) with 0 by lia. rewrite !Z.add_0_r. unfold arm.
pose proof (K (Z.of_nat j) ltac:(lia)) as E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W') m') (a' + Z.of_nat j)) as [b'|],
  (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* the byte list a garr8 sees, read back through Z_to_bv 8 *)
Lemma dt_bzs_of_garr8 : forall mem a (l : list Z), garr8 SEGS mem a l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
intros mem a l H. unfold bzs.
apply (nth_ext _ _ 0 0); [rewrite !length_map; reflexivity|].
intros j Hj. rewrite !length_map in Hj.
rewrite (nth_indep (map bz (map (Z_to_bv 8) l)) 0 (bz (Z_to_bv 8 0))) by (rewrite !length_map; exact Hj).
rewrite List.map_nth, List.map_nth, dt_bz_bv8. destruct (H j Hj) as [_ Hr]. apply Z.mod_small. exact Hr.
Qed.

(* ---- The relay entry after the growth: s->buf = res, s->cap = nc, the bytes past the copy fresh. ---- *)
Definition dt_ge (e : rentry) (res nc : Z) (junk : list byte) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) res (re_used e) nc (re_hp e) (re_kh e) (re_pad2 e) (re_keys e)
   (re_U e) junk.
(* the entry's blocks other than its buffer *)
Definition dt_hkb (e : rentry) : list (Z * Z) :=
(if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e).

(* the 56 bytes at SA after the two stores: only s->buf [16, 24) and s->cap [32, 40) changed *)
Lemma dt_entry_grow : forall (W : world SEGS) m (W' : world SEGS) m' SA e res nc junk,
length (re_pad1 e) = 4%nat -> 0 <= res < 2 ^ 64 -> 0 <= nc < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 16) 8 res -> val_mem SEGS (arm W' m') (SA + 32) 8 nc ->
(forall x, SA <= x < SA + 16 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 24 <= x < SA + 32 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 40 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
length (re_pad2 e) = 4%nat ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes (dt_ge e res nc junk))).
Proof.
intros W m W' m' SA e res nc junk Hp1 Hres Hnc H Vb Vc K1 K2 K3 Hp2.
unfold entry_bytes, re_nheld in H |- *. unfold dt_ge.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys].
rewrite !dt_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HA10]. apply garr8_app in H as [H HA9]. apply garr8_app in H as [H HA8].
apply garr8_app in H as [H _]. apply garr8_app in H as [H HA6]. apply garr8_app in H as [H4 _].
rewrite (dt_le8_bytes res Hres), (dt_le8_bytes nc Hnc).
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 52)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_keptv W m); [apply (dt_garr8_at _ _ _ _ HA10); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. rewrite ?Hp2. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 48)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_keptv W m); [apply (dt_garr8_at _ _ _ _ HA9); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 40)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_keptv W m); [apply (dt_garr8_at _ _ _ _ HA8); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K3. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 32)); [|dt_len; rewrite ?Hp1; lia].
    apply dt_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hnc | exact Vc]. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 24)); [|dt_len; rewrite ?Hp1; lia].
    apply (dt_garr8_keptv W m); [apply (dt_garr8_at _ _ _ _ HA6); dt_len; rewrite ?Hp1; lia|].
    intros x Hx. apply K2. revert Hx. dt_len. intros Hx. lia. }
apply garr8_app. split.
2:{ apply (dt_garr8_at _ (SA + 16)); [|dt_len; rewrite ?Hp1; lia].
    apply dt_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hres | exact Vb]. }
apply (dt_garr8_keptv W m); [exact H4|].
intros x Hx. apply K1. revert Hx. dt_len. rewrite ?Hp1. intros Hx. lia.
Qed.

(* the new buffer's bytes: the copy of the old buffer's cap bytes (U ++ junk), then the block's own bytes *)
Lemma dt_newbuf : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 e res nc,
((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
 (0 < re_cap e /\ Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
  garr8 SEGS (arm W1 m1) (re_buf e) (bzs (re_U e ++ re_junk e)))) ->
Z.of_nat (length (re_U e)) = re_used e -> 0 <= re_cap e <= nc ->
(0 < re_cap e -> forall i, 0 <= i < re_cap e ->
  aview SEGS (w_H W2) m2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e + i)) ->
(forall x, res <= x < res + nc -> apresent (w_H W2) m2 x) ->
exists junk, Z.of_nat (length junk) = nc - re_used e /\ garr8 SEGS (arm W2 m2) res (bzs (re_U e ++ junk)).
Proof.
intros W1 m1 W2 m2 e res nc Hb HU Hc Hcp Hpr.
assert (Hfresh : forall a k, res <= a -> a + Z.of_nat k <= res + nc ->
  exists l : list byte, length l = k /\ garr8 SEGS (arm W2 m2) a (bzs l)).
{ intros a k H1 H2.
  destruct (garr8_of_present SEGS (arm W2 m2) a k) as (l & Hl & Hg).
  { intros x Hx. destruct (Hpr x ltac:(lia)) as (Hh & bb & Hbb). exists bb.
    unfold arm, mrestrict. rewrite Hh, Hbb. reflexivity. }
  exists (map (Z_to_bv 8) l). split; [rewrite length_map; exact Hl|].
  rewrite (dt_bzs_of_garr8 _ _ _ Hg). exact Hg. }
destruct Hb as [(Hc0 & Hb0 & Hu0) | (Hcp0 & HJk & Hg)].
- assert (HU0 : re_U e = []) by (destruct (re_U e); [reflexivity | cbn [length] in HU; lia]).
  assert (Hk : res + Z.of_nat (Z.to_nat nc) <= res + nc) by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh res (Z.to_nat nc) ltac:(lia) Hk) as (l & Hl & Hg).
  exists l. rewrite HU0, Hu0. cbn [app]. split; [rewrite Hl, Z2Nat.id by lia; lia | exact Hg].
- assert (Hk : res + re_cap e + Z.of_nat (Z.to_nat (nc - re_cap e)) <= res + nc)
    by (rewrite Z2Nat.id by lia; lia).
  destruct (Hfresh (res + re_cap e) (Z.to_nat (nc - re_cap e)) ltac:(lia) Hk) as (l & Hl & Hg2).
  exists (re_junk e ++ l). split; [rewrite length_app, Nat2Z.inj_add, Hl, Z2Nat.id by lia; lia|].
  rewrite app_assoc, dt_bzs_app. apply garr8_app. split.
  + apply (dt_garr8_shift W1 m1 W2 m2 (re_buf e) res); [exact Hg|].
    intros i Hi. apply (Hcp Hcp0). rewrite dt_bzs_len, length_app, Nat2Z.inj_add in Hi. lia.
  + apply (dt_garr8_at _ _ _ _ Hg2). rewrite dt_bzs_len, length_app, Nat2Z.inj_add. lia.
Qed.

(* the entry's invariant after the growth: the new buffer block in place of the old one, the rest kept *)
Lemma dt_aentry_okx_grow : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e res nc junk,
aentry_okx B ly S W m e ->
(nc = 8192 \/ nc = 16384) -> re_used e <= nc ->
In (res, nc) (ablocks B ly' S') -> Z.of_nat (length junk) = nc - re_used e ->
garr8 SEGS (arm W' m') res (bzs (re_U e ++ junk)) ->
akept W m W' m' (gfp (re_hp e) (bzs (key_ptrs (re_keys e))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e)) ->
(forall b, In b (dt_hkb e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' m' (dt_ge e res nc junk).
Proof.
intros ly S W m ly' S' W' m' e res nc junk
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) Hnc Hu Hin Hj Hg HK HB.
unfold aentry_okx, re_nheld in *. unfold dt_ge.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [destruct Hnc as [-> | ->]; right; [left | right]; reflexivity|].
split; [exact H7|].
split; [exact Hu|].
split; [right; split; [destruct Hnc as [-> | ->]; lia|]; split; [exact Hin|]; split; [exact Hj | exact Hg]|].
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin' & Hk1 & Hk2 & Hg')]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold dt_hkb; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg'].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [left; reflexivity | exact Hx]. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold dt_hkb; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
right. apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* the live blocks after the call: the new block, the table, the entry's other blocks and the rest *)
Lemma dt_grow_perm : forall ly1 S1 ly2 S2 TB Q e res nc,
Permutation (ablocks B ly1 S1) (TB :: aentry_blks e ++ Q) ->
(re_cap e = 0 -> re_buf e = 0) -> (re_cap e <> 0 -> re_buf e <> 0) ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
Permutation (ablocks B ly2 S2) ((res, nc) :: TB :: dt_hkb e ++ Q).
Proof.
intros ly1 S1 ly2 S2 TB Q e res nc HP Hz Hnz HA HB'.
change (aentry_blks e) with ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ dt_hkb e) in HP.
revert HP. destruct (re_cap e =? 0) eqn:Ec; intros HP; cbn [app] in HP.
- apply Z.eqb_eq in Ec. eapply Permutation_trans; [exact (HA (Hz Ec))|]. apply perm_skip. exact HP.
- apply Z.eqb_neq in Ec. destruct (HB' (Hnz Ec)) as (l1 & l2 & E1 & P2).
  eapply Permutation_trans; [exact P2|]. apply perm_skip.
  apply (Permutation_cons_inv (a := (re_buf e, re_cap e))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- E1.
  eapply Permutation_trans; [exact HP|]. apply perm_swap.
Qed.

(* the live bytes after the call: at most nc more *)
Lemma dt_grow_bb : forall ly1 S1 ly2 S2 e res nc,
0 <= re_cap e ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
blocks_bytes S2 <= blocks_bytes S1 + nc.
Proof.
intros ly1 S1 ly2 S2 e res nc Hc HA HB'.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2).
destruct (Z.eq_dec (re_buf e) 0) as [Hz|Hz].
- rewrite (bsum_perm _ _ (HA Hz)), bsum_cons. cbn [snd]. lia.
- destruct (HB' Hz) as (l1 & l2 & E1 & P2). rewrite (bsum_perm _ _ P2), E1, bsum_cons, !bsum_app, bsum_cons.
  cbn [snd]. lia.
Qed.

(* C3: the live bytes after the call, exactly: the old buffer (re_cap e bytes; none when re_buf e = 0) replaced by
   the nc-byte block *)
Lemma dt_grow_bbx : forall ly1 S1 ly2 S2 e res nc,
(re_buf e = 0 -> re_cap e = 0) ->
(re_buf e = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e, re_cap e) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
blocks_bytes S2 = blocks_bytes S1 - re_cap e + nc.
Proof.
intros ly1 S1 ly2 S2 e res nc H0 HA HB'.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2).
destruct (Z.eq_dec (re_buf e) 0) as [Hz|Hz].
- rewrite (bsum_perm _ _ (HA Hz)), bsum_cons, (H0 Hz). cbn [snd]. lia.
- destruct (HB' Hz) as (l1 & l2 & E1 & P2). rewrite (bsum_perm _ _ P2), E1, bsum_cons, !bsum_app, bsum_cons.
  cbn [snd]. lia.
Qed.

(* the meter after the growth's request (C3: the live bytes after it plus the peak of the rest, from dt_grow_pk and
   dt_grow_bbx at the call site) *)
Lemma dt_grow_bud : forall cx S1 S2 spent tl tl2 (EV : list (RelayRunT.rev YO0i.sptr)) nc,
dbud MT MMAX cx S1 spent tl -> tl = EV ++ tl2 ->
tr_cost MT EV = mo_malloc MT nc + mo_free MT -> tr_max EV = nc ->
0 <= mo_malloc MT nc + mo_free MT ->
mo_le MT S1 S2 (mo_malloc MT nc + mo_free MT) ->
blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX ->
dbud MT MMAX cx S2 (spent + (mo_malloc MT nc + mo_free MT)) tl2.
Proof.
intros cx S1 S2 spent tl tl2 EV nc (Hle & Hsp & Hcost & Hlv & Hmax) Etl Hc Hm Hc0 HMO HBB.
rewrite Etl, dt_tr_cost_app, Hc in Hcost.
rewrite Etl, dt_tr_max_app, Hm in Hmax.
split; [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle HMO)|].
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* The memory core of DT1 after the call and the two stores, from realloc #1's post (on mem2) and what the
   stretch 0x8324c .. 0x8326c leaves (m3: every byte but s->buf and s->cap as the call left it, presence grown,
   s->buf = res, s->cap = nc).  The entry becomes dt_ge e1 res nc junk: the buffer is the new block, its first
   cap bytes the copy of the old buffer's U ++ junk, the rest of it the block's own bytes. *)
Lemma dt_grow_core : forall cx s1 (W1 : world SEGS) ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1
  (W2 : world SEGS) ly2 S2 mem2 md2 m3 md3 res nc,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1 ->
DLINK s1 e1 h1 -> re_used e1 <= APARTIAL ->
drain_b_c.ds_cap (dgrow s1) = nc ->
nc = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) -> 8192 <= nc <= 16384 ->
AR SEGS B ly2 S2 W2 mem2 md2 -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) nc ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m3 md3 (k1 + 3) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W2) mem2 x) ->
(forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m3 x) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 16) 8 res ->
val_mem SEGS (arm W2 m3) (dxSA cx + 32) 8 nc ->
exists junk,
  DMEM B RG cx ly2 S2 W2 m3 md3 (k1 + 3) (dt_ge e1 res nc junk) h1 (dgrow s1) out1 ev1 sent LB1 /\
  DLINK (dgrow s1) (dt_ge e1 res nc junk) h1.
Proof.
intros cx s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 W2 ly2 S2 mem2 md2 m3 md3 res nc
  HB HMEM HLINK Hused Enc Hncap Hnb HAR2 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ3 KV KP V16 V32.
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
pose proof HMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT &
  HLIVE & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (FB : alloc_ceiling + DRAIN_STK <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (AR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (AR3 : AR SEGS B ly2 S2 W2 m3 md3) by (eapply ajournal_gx_AR; exact HJ3).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HU & Hucap & HBUF & _ & HHP & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSAle' : dxSA cx + 56 <= dxG cx + 896) by (clear - HSAle; unfold AENT, ATABLE in HSAle; lia).
assert (Hcn : re_cap e1 <= nc /\ (nc = 8192 \/ nc = 16384)).
{ clear - Hncap Hnb Hcapv. destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in Hncap; cbn [Z.eqb] in Hncap; lia. }
assert (RQN : req_size nc = nc) by (unfold req_size; destruct (Z.eqb_spec nc 0) as [E0|E0]; [lia | reflexivity]).
(* ---- the live blocks before and after the call ---- *)
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> 4096 <= re_buf e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ AR1 Hin) as (_ & H4 & _). split; [exact H4 | exact Hin]. }
assert (Hnz' : re_cap e1 <> 0 -> re_buf e1 <> 0) by (intros Hc; destruct (Hnz Hc) as (H4 & _); lia).
pose proof (dt_grow_perm ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res nc HPERM Hz Hnz' HpermA HpermB)
  as P2.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, nc)).
pose (R := asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
pose (Q := dt_hkb e1 ++ R).
change (Permutation (ablocks B ly2 S2) (NB :: TB :: Q)) in P2.
assert (P2T : Permutation (ablocks B ly2 S2) (TB :: NB :: Q))
  by (eapply Permutation_trans; [exact P2 | apply perm_swap]).
assert (P1 : Permutation (ablocks B ly1 S1) (TB :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ Q)).
{ eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
  change (aentry_blks e1) with ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ dt_hkb e1).
  rewrite <- app_assoc. apply Permutation_refl. }
assert (Q1 : forall b, In b (TB :: Q) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). destruct Hb as [<-|Hb]; [left; reflexivity|].
  right. apply in_or_app. right. exact Hb. }
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2T)); left; reflexivity).
assert (Q2 : forall b, In b Q -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P2)); right; right; exact Hb).
assert (DNB : forall b, In b (TB :: Q) -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head ly2 S2 W2 mem2 md2 NB (TB :: Q) b HAR2 P2 Hb)).
assert (DOB : re_cap e1 <> 0 -> forall b, In b (TB :: Q) ->
  zdisjoint (block_rng (re_buf e1, re_cap e1)) (block_rng b)).
{ intros Hc b Hb. apply (dt_sep_head ly1 S1 W1 m1 md1 _ (TB :: Q) b AR1); [|exact Hb].
  eapply Permutation_trans; [exact P1|]. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [app]. apply perm_swap. }
assert (DTQ : forall b, In b Q -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head ly2 S2 W2 mem2 md2 TB (NB :: Q) b HAR2 P2T (or_intror Hb))).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE AR1 (Q1 TB (or_introl eq_refl)))
  as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 res nc AR3 NB2) as (_ & HN4 & HNcl & _ & HNpr & _).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 (dxG cx) ATABLE AR3 TB2) as (_ & _ & _ & _ & HTpr & _).
rewrite RQN in HNcl, HNpr. rewrite RQT in HTpr.
(* ---- what the call keeps of the table and the entry's other blocks ---- *)
assert (KC : forall b x, In b (TB :: Q) -> fst b <= x < fst b + req_size (snd b) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. pose proof Hkept2 as (_ & K2 & _).
  replace x with (pb + (x - pb)) by ring. apply (K2 pb mb (x - pb) (Q1 _ Hb)); [lia|].
  replace (pb + (x - pb)) with x by ring. cbv beta.
  intros [Hn | (Hb0 & Ho)].
  - pose proof (DNB _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj. lia.
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    pose proof (DOB Hc _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj. lia. }
(* ---- and what the stores keep ---- *)
assert (KO : forall b x, In b Q -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m3 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx.
  pose proof (DTQ _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 m3 md3 pb mb AR3 (Q2 _ Hb)) as (_ & H4 & Hcl & _ & Hpr & _).
  assert (Hr : 0 <= x < 2 ^ 64) by lia.
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x Hr N1 N2). exact (KC (pb, mb) x (or_intror Hb) Hx).
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (FK : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64)
    by (clear - Hx FB HAC; unfold DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x ltac:(lia) N1 N2). exact (K1 x Hr1 Hr2).
  - intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
    intros Hp. apply KP. exact (K5 x Hr1 Hr2 Hp). }
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 16 <= x < dxSA cx + 24) /\ ~ (dxSA cx + 32 <= x < dxSA cx + 40)).
{ intros x Hx. split; intros Hw;
    exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE x AR1 (Q1 TB (or_introl eq_refl))
      ltac:(rewrite RQT; lia) Hx). }
assert (APK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m3 x).
{ intros x Hi Hno Herr Hp.
  assert (Hnot : forall ly0 S0 (W0 : world SEGS) m0 md0, AR SEGS B ly0 S0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (al_owned_image SEGS B LAWS ly0 S0 W0 m0 md0 x HA Hi) Ho)).
  apply KP. apply (Hpres2 x Hi (Hnot _ _ _ _ _ AR1) (Hnot _ _ _ _ _ HAR2) Herr); [|exact Hp].
  intros [Hn | (Hb0 & Ho)].
  - exact (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 res nc x HAR2 NB2 Hn Hi).
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) x AR1 (proj2 (Hnz Hc)) Ho Hi). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  assert (Hi : in_img SEGS x) by exact (proj1 (HG x Hg)).
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  assert (EV : aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KV x Hr N1 N2). replace x with (as_errno B + (x - as_errno B)) by ring. apply Herr2.
    clear - Hx; lia. }
  split; [exact EV|]. intros _.
  apply dt_img_wr; [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [destruct (HG x Hx) as (Gi & Gn & _) | destruct (HGO x Hx) as (Gi & Gn & _)]; exact (conj Gi Gn)).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  pose proof Hkept2 as (_ & _ & K3 & _).
  split; [rewrite (KV x Hr N1 N2); exact (K3 x Hi Ho Hne)|].
  intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
  intros Hp. exact (APK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + 56 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
  ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite (KV x ltac:(lia) N1 N2).
  apply (KC TB x (or_introl eq_refl)). unfold TB. cbn [fst snd]. rewrite RQT. lia. }
(* ---- the entry: the new buffer, its bytes and the 56 bytes at SA ---- *)
assert (CP3 : 0 < re_cap e1 -> forall i, 0 <= i < re_cap e1 ->
  aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)).
{ intros Hc i Hi.
  pose proof (DNB TB (or_introl eq_refl)) as Dj. unfold zdisjoint, block_rng, NB, TB in Dj. cbn [fst snd] in Dj.
  rewrite RQT, RQN in Dj.
  rewrite (KV (res + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Hcopy; [destruct (Hnz ltac:(lia)) as (H4 & _); lia | rewrite Z.min_l by lia; exact Hi]. }
assert (HBUF' : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (destruct HBUF as [Hq|(Hq1 & _ & Hq3 & Hq4)]; [left; exact Hq | right; exact (conj Hq1 (conj Hq3 Hq4))]).
assert (Hcb : 0 <= re_cap e1 <= nc) by (destruct Hcapv as [Hq|[Hq|Hq]]; lia).
destruct (dt_newbuf W1 m1 W2 m3 e1 res nc HBUF' HU Hcb CP3 (fun x Hx => proj1 (HNpr x Hx)))
  as (junk & Hjl & Hjg).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
assert (Hnc64 : 0 <= nc < 2 ^ 64) by lia.
assert (ENT3 : garr8 SEGS (arm W2 m3) (dxSA cx) (bzs (entry_bytes (dt_ge e1 res nc junk)))).
{ apply (dt_entry_grow W1 m1 W2 m3 (dxSA cx) e1 res nc junk Hp1 Hres64 Hnc64 HENTB V16 V32); [| | | exact Hp2];
    intros x Hx; apply TK; lia. }
assert (AWR3 : awr W2 m3 (dxSA cx) AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  apply (proj1 (HTpr (dxSA cx + i) ltac:(unfold AENT in Hi; lia))). }
assert (AK : akept W1 m1 W2 m3 (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e1))).
{ intros r Hr x Hx. destruct Hr as [<- | Hr].
  - unfold gfp in Hx. cbn [fst snd] in Hx. rewrite dt_bzs_len, dt_key_ptrs_len in Hx.
    destruct HHP as [(Hz0 & Hk0) | (Hz0 & HinH & Hk1 & Hk2 & _)].
    + rewrite Hk0 in Hx. cbn [length] in Hx. lia.
    + apply (KO (re_hp e1, re_kh e1) x).
      * unfold Q, dt_hkb. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz0).
        apply in_or_app. left. left. reflexivity.
      * cbn [fst snd]. unfold re_nheld in Hk1. pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & RQ). lia.
  - apply in_map_iff in Hr as (k & <- & Hk).
    apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
    + unfold Q, dt_hkb. apply in_or_app. left. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    + unfold gfp in Hx. cbn [fst snd] in Hx |- *. rewrite dt_bzs_len, length_app in Hx. cbn [length] in Hx.
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). lia. }
assert (OKX3 : aentry_okx B ly2 S2 W2 m3 (dt_ge e1 res nc junk)).
{ apply (dt_aentry_okx_grow ly1 S1 W1 m1 ly2 S2 W2 m3 e1 res nc junk HOKX (proj2 Hcn)
    ltac:(unfold APARTIAL in Hused; lia) NB2 Hjl Hjg AK).
  intros b Hb. apply Q2. unfold Q. apply in_or_app. left. exact Hb. }
(* ---- the harness source, the other slots, g_s, the output ---- *)
assert (SRC3 : asrc_at B ly2 S2 W2 m3 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m3 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct (dt_src_fp ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold Q, R. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply Q2. unfold Q, R. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (OTH3 : aothers_at RG W2 m3 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & Va & Vb & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m3) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact Va] | split; [apply GV; [| | exact Vb] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK3 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m3 x)
  by (intros x H1 H2; exact (dt_bk_trans _ _ W1 m1 W2 m3 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT3 : aout_at B RG ly2 S2 W2 m3 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m3 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (dt_out_fp _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, drain_b_c.ds_ocap s1) x).
    + unfold Q, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply Q2. unfold Q, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (ROM3 : rom_view SEGS W2 m3).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) (dt_in_zr_dec x)) as [Hown | Hno].
  - eapply rom_pinned_view; [exact AR3 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    destruct (NIMG x Hi) as (N1 & N2).
    assert (Hr : 0 <= x < 2 ^ 64)
      by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
    pose proof Hkept2 as (_ & _ & K3 & _).
    rewrite (KV x Hr N1 N2), (K3 x Hi Hno Hne). exact (HROM x Hx). }
assert (PK3 : apres_kept B (dxW cx) (dxmem cx) W2 m3)
  by (intros x Hi Ho He Hp; exact (APK x Hi Ho He (HPRESK x Hi Ho He Hp))).
assert (EA2 : aentry_blks (dt_ge e1 res nc junk) = NB :: dt_hkb e1).
{ unfold aentry_blks, dt_ge, dt_hkb. cbn [re_cap re_buf re_hp re_kh re_keys].
  rewrite (proj2 (Z.eqb_neq nc 0) ltac:(lia)). reflexivity. }
exists junk. split.
- unfold DMEM.
  refine (conj HJ3 (conj ROM3 (conj PK3 (conj (eq_trans Hfrs2 HFRM) (conj (dt_frame_kept cx W1 m1 W2 m3 FK HFRAME)
    (conj ENT3 (conj AWR3 (conj OKX3 (conj SRC3 (conj OTH3 (conj GSK3 (conj OUT3 (conj HLIVE _))))))))))))).
  rewrite EA2. exact P2T.
- pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj (eq_sym Enc) (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10
    (conj K11 K12))))))))))).
Qed.


Lemma dt_aout_nn : forall ly S (W : world SEGS) m c O mx no cap out,
aout_at B RG ly S W m c O mx no cap out -> 0 <= no /\ 0 <= cap /\ 0 <= mx <= 255.
Proof.
intros ly S W m c O mx no cap out H. unfold aout_at in H. clear - H.
repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end.
split; [lia|]. split; [|lia].
match goal with Hq : (cap = 0 /\ _) \/ _ |- _ => destruct Hq as [(Hc & _)|(Hc & _)] end; lia.
Qed.

Lemma dt_entry_kh : forall ly S (W : world SEGS) m e,
aentry_okx B ly S W m e -> (re_hp e =? 0) = false -> 0 <= re_kh e.
Proof.
intros ly S W m e H Hz. unfold aentry_okx in H. clear - H Hz.
repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end.
apply Z.eqb_neq in Hz.
match goal with Hq : (re_hp e = 0 /\ _) \/ _ |- _ =>
  destruct Hq as [(Hc & _)|(_ & _ & _ & Hk & _)] end; lia.
Qed.

Lemma dt_src_ecap : forall ly S (W : world SEGS) m HA h,
asrc_at B ly S W m HA h -> 0 <= hl_cap (hs_expected h).
Proof.
intros ly S W m HA h H. unfold asrc_at in H. clear - H.
repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end.
match goal with Hq : alist_at B ly S W m (HA + 64) (hs_expected h) true |- _ =>
  unfold alist_at in Hq; repeat match goal with Hr : _ /\ _ |- _ => destruct Hr end end.
match goal with Hq : (hl_cap (hs_expected h) = 0 /\ _) \/ _ |- _ =>
  destruct Hq as [(Hc & _)|(Hc & _)] end; lia.
Qed.

(* ==== [B] GROW: DI 0x833c0 with cap - used < 4096 -> realloc #1 (0x83410) -> DT1 0x83438. ====
   Before the call the stretch reads the frame's three shadow slots (216 = shadow(SA + 32), 232 = shadow(SA + 24),
   224 = shadow(SA + 16)) and the entry's cap / used / buf; on image B the shadow addresses are frame slots, not
   registers, and SHADOW_OFF is the extra atom 35.  Nothing is stored before the call.  The capacity the round
   asks for is in s3 (A: s4), the buffer in a0.  After the call the two stores write s->buf [SA+16, SA+24) at
   0x83424 and s->cap [SA+32, SA+40) at 0x83434, each behind its own shadow check (frame 224, then 216). *)
Definition A_dr_rret : Z := AF_fr_drain + 0x19c.

Definition dt_gr_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 0 0
  [ YP09.mkChunk 216 (dt_shA 32 32); YP09.mkChunk 224 (dt_shA 32 16); YP09.mkChunk 232 (dt_shA 32 24) ].
Definition dt_gr_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 16 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition dt_gr_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF SB SB 0); (8%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0) ] [] [].
Definition ss_gr : sstate := mkSS A_dr_top dt_regs_top [ dt_gr_frame; dt_gr_sa ] None dt_gr_facts.
Definition dt_gr_extra (SA cap used buf : Z) : list word :=
  map (Z_to_bv 64) [SA; cap; used; SHADOW_OFF; buf].

Definition dt_gp_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 0 0
  [ YP09.mkChunk 216 (dt_shA 32 32); YP09.mkChunk 224 (dt_shA 32 16) ].
Definition dt_gp_buf : YP09.region := YP09.mkRegion (Some 32%nat) 16 24 16 24 [].
Definition dt_gp_cap : YP09.region := YP09.mkRegion (Some 32%nat) 32 40 32 40 [].
Definition dt_gp_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF SB SB 0); (8%nat, dt_IMGF); (32%nat, dt_HEAPF) ] [] [].
Definition ss_gp : sstate := mkSS A_dr_rret dt_regs_top [ dt_gp_frame; dt_gp_buf; dt_gp_cap ] None dt_gp_facts.
Definition dt_gp_extra (SA : Z) : list word := map (Z_to_bv 64) [SA; 0; 0; SHADOW_OFF].

Lemma dt_grow_post : forall cx s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl
  memS (W2 : world SEGS) ly2 S2 regs2 mem2 md2 res tl2,
DBASE B MT MMAX RG cx ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud MT MMAX cx S1 spent tl ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) ->
8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384 ->
tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)) ++ tl2 ->
dlater cx (dgrow s1)
  (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa))))
  (agrow s1 jb aa) tl2 ->
0 <= DRAIN_STK -> gagree (G_DR B RG) (w_H (dxW cx)) (dxmem cx) memS ->
ajournal SEGS B DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS (dxmd cx) []
  ly2 S2 W2 mem2 md2 (k1 + 3) ->
aregs_preserved regs1 regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2)
   ((res, drain_b_c.ds_cap (dgrow s1)) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, drain_b_c.ds_cap (dgrow s1)) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
            (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
mo_le MT S1 S2 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
      (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
(forall W3 c3, DT1 cx (dgrow s1) D W3 c3 -> SRr SEGS W3 c3 (dPOST B MT RG cx)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)) md2) (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS W2 ly2 S2 regs2 mem2 md2 res tl2
  HB Hregs Hra R10 R11 R19
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2i HPR Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 Herr2 Hpres2 K.
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HAR2 : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2i).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR1 HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HUl & Hucap & HBUF & _).
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> re_buf e1 <> 0).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & _). lia. }
pose proof (dt_grow_perm ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res (drain_b_c.ds_cap (dgrow s1))
  Hperm Hz Hnz HpermA HpermB) as HP2.
assert (TB2 : In (dxG cx, ATABLE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); right; left; reflexivity).
assert (NB2 : In (res, drain_b_c.ds_cap (dgrow s1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 NB2) as (_ & _ & HNcl & _).
pose proof (req_size_pos (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)) as (_ & RQN).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (dxG cx) ATABLE HAR2 TB2) as (_ & _ & _ & _ & HTP2 & _).
assert (FK0 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 mem2 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64) by (clear - Hx HspA HspB; unfold DRAIN_FRAME in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  split; [exact (K1 x Hr1 Hr2)|]. intros Hw.
  apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 mem2 x); [|exact Hw]. exact (K5 x Hr1 Hr2). }
pose proof (dt_frame_kept cx W1 m1 W2 mem2 FK0 HFR) as HFR2.
pose proof HFR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F216' & F224' & _).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (P2 : getr regs2 2 = getr regs1 2) by (apply PR; dt_cs).
assert (P3 : getr regs2 3 = getr regs1 3) by (apply PR; dt_cs).
assert (P4 : getr regs2 4 = getr regs1 4) by (apply PR; dt_cs).
assert (P8 : getr regs2 8 = getr regs1 8) by (apply PR; dt_cs).
assert (P9 : getr regs2 9 = getr regs1 9) by (apply PR; dt_cs).
assert (P18 : getr regs2 18 = getr regs1 18) by (apply PR; dt_cs).
assert (P19 : getr regs2 19 = getr regs1 19) by (apply PR; dt_cs).
assert (P20 : getr regs2 20 = getr regs1 20) by (apply PR; dt_cs).
assert (P21 : getr regs2 21 = getr regs1 21) by (apply PR; dt_cs).
assert (P22 : getr regs2 22 = getr regs1 22) by (apply PR; dt_cs).
assert (P24 : getr regs2 24 = getr regs1 24) by (apply PR; dt_cs).
assert (P26 : getr regs2 26 = getr regs1 26) by (apply PR; dt_cs).
assert (P27 : getr regs2 27 = getr regs1 27) by (apply PR; dt_cs).
unfold w64.
remember (Eimg (Ereg regs2 (dt_gp_extra (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hr)).
assert (E2 : ew E 2 = getr regs2 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs2 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs2 4) by (apply EREG; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 res)
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact Hres10).
assert (E19 : ew E 19 = Z_to_bv 64 (drain_b_c.ds_cap (dgrow s1)))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite P19; exact R19).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); rewrite P8; exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2, P2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (R21' : getr regs2 21 = sv_denot E (SOff 32 0))
  by (rewrite P21, (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs2 24 = sv_denot E (SOff 32 8))
  by (rewrite P24, (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs2 20 = sv_denot E (SOff 32 16))
  by (rewrite P20, (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs2 22 = sv_denot E (SOff 32 24))
  by (rewrite P22, (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs2 27 = sv_denot E (SOff 32 32))
  by (rewrite P27, (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs2 9 = sv_denot E (dt_gv 0))
  by (rewrite P9, (dt_den_gv E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs2 18 = sv_denot E (dt_gv 4))
  by (rewrite P18, (dt_den_gv E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs2 26 = sv_denot E (SLit 384))
  by (rewrite P26, denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_gp
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gp. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gp_frame, dt_gp_buf, dt_gp_cap;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact (dt_den_sh E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia); zside])
          | zside | exact F216' ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh E 32 (dxSA cx) 16 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia); zside])
          | zside | exact F224' ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
  - apply pairwise_disjoint_of_extents. unfold dt_gp_frame, dt_gp_buf, dt_gp_cap, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gp_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W2) mem2)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly2 S2 W2 mem2 md2 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR2 TB2).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
pose proof (dt_gx_close (G_DR B RG) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 3) memS HSTK HAG HJ2i) as HJ2.
psrr_branch_tok RUN BR HS SHOK DBspan.
- exfalso. rewrite (dt_beqz_atom E 10 res E10 Hres64) in Hc. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok RUNTO HS HJ2 SHOK DBspan A_dr_mid.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa0 Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_nil. }
  rewrite ?wvb_collapse in HJ2.
  assert (Hnw : forall x, ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
    ~ in_wrange E (ss_mem ss_gp) x).
  { intros x N1 N2 (r & Hin & Hr). cbv [ss_mem ss_gp dt_gp_frame dt_gp_buf dt_gp_cap] in Hin.
    destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?U32 in Hr; lia. }
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
    ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x)
    by (intros x Hx N1 N2; exact (aview_kept_out E _ (w_H W2) mem2 (ms_mem ms) HFr x Hx (Hnw x N1 N2))).
  assert (KP : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ _ HG0 Hx)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RB.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RC.
  cbn [ms_mem restrict] in RB, RC.
  assert (V16 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 16) 8 res).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 16 8%N (SOff 10 0) res RB U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 10 res E10 Hres64).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V32 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 32) 8 (drain_b_c.ds_cap (dgrow s1))).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 32 8%N (SOff 19 0) (drain_b_c.ds_cap (dgrow s1))
      RC U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 19 (drain_b_c.ds_cap (dgrow s1)) E19 ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3. dt_reg HS (4%bv : bv 5) X4.
  dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9. dt_reg HS (18%bv : bv 5) X18.
  dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21. dt_reg HS (22%bv : bv 5) X22.
  dt_reg HS (24%bv : bv 5) X24. dt_reg HS (26%bv : bv 5) X26. dt_reg HS (27%bv : bv 5) X27.
  pmkst HS.
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUl).
  destruct (dt_grow_ev (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
    ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
  change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
  assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
  { pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
    pose proof (mo_free_nonneg MT MTL). lia. }
  assert (Hb0 : re_buf e1 = 0 -> re_cap e1 = 0)
    by (intros Hb; destruct (Z.eq_dec (re_cap e1) 0) as [Hq|Hq]; [exact Hq | exfalso; exact (Hnz Hq Hb)]).
  pose proof (dt_grow_bbx ly1 S1 ly2 S2 e1 res (drain_b_c.ds_cap (dgrow s1)) Hb0 HpermA HpermB) as HBB.
  assert (HBB2 : blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX).
  { pose proof Hbud as (_ & _ & _ & Hlv & _). rewrite Htl in Hlv.
    destruct (dt_grow_pk (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
      ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlv) as (_ & Hpk).
    change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hpk.
    rewrite <- Lcap in Hpk. lia. }
  pose proof (dt_grow_bud cx S1 S2 spent tl tl2 _ (drain_b_c.ds_cap (dgrow s1)) Hbud Htl Hev_co Hev_max
    HmoN Hmle2 HBB2) as HBUD2.
  destruct (dt_grow_core cx s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 W2 ly2 S2 mem2 md2
    (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1)) HB HMEM HLINK Hused eq_refl Hncap Hnb HAR2 Hfrs2 Hres4096
    HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ2 KV KP V16 V32) as (junk & HDM & HDL).
  apply K. unfold DT1.
  eexists _, ly2, S2, _, _, (k1 + 3), (dt_ge e1 res (drain_b_c.ds_cap (dgrow s1)) junk), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)), _, (agrow s1 jb aa), tl2.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2), P2; exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3), P3; exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4), P4; exact R4|].
    split; [rewrite X21; exact (eq_trans (eq_sym R21') (eq_trans P21 R21))|].
    split; [rewrite X24; exact (eq_trans (eq_sym R24') (eq_trans P24 R24))|].
    split; [rewrite X20; exact (eq_trans (eq_sym R20') (eq_trans P20 R20))|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') (eq_trans P22 R22))|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') (eq_trans P27 R27))|].
    split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') (eq_trans P9 R9))|].
    split; [rewrite X18; exact (eq_trans (eq_sym R18') (eq_trans P18 R18))
           |rewrite X26; exact (eq_trans (eq_sym R26') (eq_trans P26 R26))]. }
  split; [exact HDM|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split; [unfold dinband, dt_ge; cbn [re_buf re_cap];
    pose proof YM05.alloc_ceiling_lt as HAC; unfold DCEIL;
    (split; [lia|]); (split; [lia|]); apply (Z.mod_divide res 8 ltac:(lia));
    destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1))
      ltac:(eapply ajournal_gx_AR; exact HJ2) NB2) as (Hm16 & _);
    apply Z.mod_divide in Hm16; [|lia]; destruct Hm16 as (q & ->); exists (2 * q); lia|].
  split; [exact HDL|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Hlater2 | exact HBUD2].
Qed.


Lemma dt_grow_after : forall cx s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl,
DBASE B MT MMAX RG cx ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud MT MMAX cx S1 spent tl ->
(forall W2 c2, DT1 cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1) (dPOST B MT RG cx).
Proof.
intros cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
  Hregs Hra R10 R11 R19 HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K.
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; clear - Hceil Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; lia).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (clear - Hcapv; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hroom : 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1)).
{ apply dt_grow_room; [exact Hlt | rewrite Hulen; clear - Hused Husedb; unfold APARTIAL in Hused |- *; lia
  | rewrite Hulen, <- Lcap; exact Hucap | rewrite <- Lcap; exact Hcapv ]. }
assert (Hncap : drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2)).
{ change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
  rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; exact Hucap) Hlt),
    <- Lcap. reflexivity. }
assert (Hnb : 8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384)
  by (rewrite Hncap; clear - Hcapv Hused Hucap Hlt Lcap Hulen; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in *;
      cbn [Z.eqb]; [lia | lia | unfold APARTIAL in Hused; lia]).
destruct (dt_grow_tr cx s1 jb aa tl Hlater Hroom) as (tl2 & Htl & Hlater2).
assert (HDINV : dinv (dgrow s1)).
{ unfold dinv.
  change (drain_b_c.ds_ka (dgrow s1)) with (drain_b_c.ds_ka s1).
  change (drain_b_c.ds_ecap (dgrow s1)) with (drain_b_c.ds_ecap s1).
  change (drain_b_c.ds_ocap (dgrow s1)) with (drain_b_c.ds_ocap s1).
  change (drain_b_c.ds_no (dgrow s1)) with (drain_b_c.ds_no s1).
  pose proof HLINK as (_ & _ & _ & _ & Lka & _ & _ & _ & _ & _ & Lec & _).
  pose proof HHIST as (_ & _ & _ & _ & _ & Hno & _).
  destruct (dt_aout_nn ly1 S1 W1 m1 _ _ _ _ _ _ Hout) as (_ & Hoc0 & _).
  pose proof (dt_src_ecap ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc) as Hec.
  assert (Hka0 : 0 <= drain_b_c.ds_ka s1)
    by (rewrite <- Lka; unfold drain_b_c.ent_ka; destruct (re_hp e1 =? 0) eqn:Ehp; [lia|];
        pose proof (dt_entry_kh ly1 S1 W1 m1 e1 HEOK Ehp) as Hk; clear - Hk; lia).
  assert (Hno1 : 0 <= drain_b_c.ds_no s1).
  { rewrite Hno. pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hout0 & _).
    destruct (dt_aout_nn (dxly cx) (dxS cx) (dxW cx) (dxmem cx) _ _ _ _ _ _ Hout0) as (Hn0 & _).
    clear - Hn0; lia. }
  split; [clear - Hnb; lia|]. split; [exact Hka0|].
  split; [rewrite <- Lec; exact Hec|]. split; [exact Hoc0 | exact Hno1]. }
destruct (dt_later_meters cx (dgrow s1) _ _ tl2
  ltac:(destruct (dt_aout_nn ly1 S1 W1 m1 _ _ _ _ _ _ Hout) as (_ & _ & Hmx); clear - Hmx; lia) HDINV Hlater2)
  as (Hal2 & Hco2).
destruct (dt_grow_ev (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
  ltac:(rewrite <- Lcap; clear - Hcapb; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
pose proof Hbud as (Hmle & Hspent & Hcost & Hlive & Hmax).
rewrite Htl, dt_tr_max_app, Hev_max in Hmax.
rewrite Htl in Hlive.
destruct (dt_grow_pk (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
  ltac:(rewrite <- Lcap; clear - Hcapb; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlive) as (Hlv1 & _).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hlv1.
rewrite Htl, dt_tr_cost_app, Hev_co in Hcost.
assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(clear - Hnb; lia)) as M1.
  pose proof (mo_free_nonneg MT MTL) as M2. clear - M1 M2; lia. }
assert (Hbufc : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
   Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpn : re_buf e1 = 0 \/ In (re_buf e1, re_cap e1) (ablocks B ly1 S1))
  by (destruct Hbufc as [(_ & Hq & _)|(_ & Hq & _)]; [left; exact Hq | right; exact Hq]).
destruct (dt_gx_open (G_DR B RG) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W1 m1 md1 k1 HJ) as (memS & HSTK & HAG & HJi).
eapply SRr_bind.
{ eapply (AREALLOC W1 regs1 m1 DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) memS (dxmd cx) []
    ly1 S1 md1 k1 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) (- DRAIN_FRAME)
    (w64 (BASE + A_dr_rret)) [] HJi).
  - exact Hpn.
  - exact R10.
  - exact R11.
  - clear - Hnb Hmax Hal2. lia.
  - clear - Hlv1. lia.
  - rewrite Hsp. unfold dsp0, DRAIN_FRAME. clear. lia.
  - reflexivity.
  - unfold DRAIN_FRAME. clear. lia.
  - assert (Hq : ASTACK - - DRAIN_FRAME <= DRAIN_STK) by (vm_compute; discriminate). exact Hq.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact Hra.
  - unfold w64. apply ret_ok_codeptr_v; [unfold A_dr_rret, AF_fr_drain; lia
    | unfold A_dr_rret, AF_fr_drain; reflexivity].
  - apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) (rg_s RG) [] regs1).
    + apply achain_low. clear - HGS1 HGS2 C1. lia.
    + clear - HspA HspB Hsp. unfold DRAIN_FRAME in *. lia.
    + unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. clear - HGS1 HGS2. lia.
    + unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small
        by (unfold A_dr_rret, AF_fr_drain; clear - HBASE HBLO; lia). unfold A_dr_rret, AF_fr_drain. clear - HBASE HBLO; lia.
  - unfold raZ. cbn [spine map]. rewrite Hra. unfold w64. rewrite unsigned_lit_small
      by (unfold A_dr_rret, AF_fr_drain; clear - HBASE HBLO; lia).
    replace (BASE + A_dr_rret) with (BASE + AF_fr_drain + 0x19c) by (unfold A_dr_rret; ring). exact HCTX_re1.
  - intros Hp0 Hin0 i Hi.
    assert (Hcap0 : 0 < re_cap e1)
      by (clear - Hbufc Hp0; destruct Hbufc as [(_ & Hq & _)|(Hq & _)]; [contradiction | lia]).
    assert (Hinbl : In (re_buf e1, re_cap e1) (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1)).
    { apply in_or_app. left. unfold aentry_blks.
      assert (Ec : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; clear - Hcap0; lia). rewrite Ec. left. reflexivity. }
    pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
    apply (dt_buf_fp cx ly1 S1 W1 m1 md1 (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1) (re_buf e1) (re_cap e1) HAR);
      [ (try rewrite <- !app_assoc); exact Hperm | exact Hinbl
      | (try rewrite <- !app_assoc); exact Hperm0 | exact Hin0 | clear - Hcapb; lia
      | clear - Hcap0 Hcapv; unfold ATABLE; lia | exact Hi ].
  - pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmo0).
    apply (dt_mo_ok_of cx S1 spent tl); [exact Hmo0 | exact Hbud | exact HmoN|].
    rewrite Htl, dt_tr_cost_app, Hev_co. clear - Hco2. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2 & HJ2 & Hpres' & Hres10 & Hfrs2 &
  Hres4096 & HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & Herr2 & Hpres2).
subst c2.
exact (dt_grow_post cx s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS
  W2 ly2 S2 regs2 mem2 md2 res tl2 HB Hregs Hra R10 R11 R19
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2 Hpres' Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 Herr2 Hpres2 K).
Qed.

Theorem dt_grow : dt_grow_stmt.
Proof.
intros cx s1 D W1 c1 HB HDI Hlt K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 &
  F152 & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & _); lia).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_gr_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_gr
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gr. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gr_frame, dt_gr_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact (dt_den_sh E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh E 32 (dxSA cx) 16 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh E 32 (dxSA cx) 24 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F232 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 36 0) (re_buf e1));
          [exact (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_buf W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_used W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact (dt_entry_cap W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_gr_frame, dt_gr_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gr_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUN BR HS SHOK DBspan.
- rewrite (dt_bnez_room E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_le in Hc. rewrite <- Lcap, Hulen in Hlt. lia.
- paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  all: rewrite (dt_bnez_atom E 33 (re_cap e1) E33 ltac:(lia)) in Hc0.
  + apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = re_cap e1 * 2).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap. apply Z.eqb_neq in Hc0. rewrite Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (26%bv : bv 5) X26.
    dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    refine (dt_grow_after cx s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
      _ _ _ _ _ (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K).
    * unfold dregs_top.
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
      split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
      split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
      split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
      split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
      split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
      split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
      split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
      split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
             |rewrite X26; exact (eq_trans (eq_sym R26') R26)].
    * rewrite X1. change 240%nat with A_TEXT. rewrite (codeptr_val E 4304 HEI).
      unfold w64, A_dr_rret, AF_fr_drain. f_equal; lia.
    * rewrite X10, (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)). reflexivity.
    * rewrite X11, (dt_den_sll E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc. reflexivity.
    * rewrite X19, (dt_den_sll E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc. reflexivity.
  + apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply dt_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = 8192).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap, Hc0. reflexivity. }
    dt_reg HS (1%bv : bv 5) X1. dt_reg HS (2%bv : bv 5) X2. dt_reg HS (3%bv : bv 5) X3.
    dt_reg HS (4%bv : bv 5) X4. dt_reg HS (8%bv : bv 5) X8. dt_reg HS (9%bv : bv 5) X9.
    dt_reg HS (10%bv : bv 5) X10. dt_reg HS (11%bv : bv 5) X11. dt_reg HS (18%bv : bv 5) X18.
    dt_reg HS (19%bv : bv 5) X19. dt_reg HS (20%bv : bv 5) X20. dt_reg HS (21%bv : bv 5) X21.
    dt_reg HS (22%bv : bv 5) X22. dt_reg HS (24%bv : bv 5) X24. dt_reg HS (26%bv : bv 5) X26.
    dt_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    refine (dt_grow_after cx s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
      _ _ _ _ _ (dt_DMEM_kept cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K).
    * unfold dregs_top.
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
      split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
      split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
      split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
      split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
      split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
      split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
      split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
      split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
             |rewrite X26; exact (eq_trans (eq_sym R26') R26)].
    * rewrite X1. change 240%nat with A_TEXT. rewrite (codeptr_val E 4304 HEI).
      unfold w64, A_dr_rret, AF_fr_drain. f_equal; lia.
    * rewrite X10, (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)). reflexivity.
    * rewrite X11, Hnc. cbn [sv_denot]. reflexivity.
    * rewrite X19, Hnc. cbn [sv_denot]. reflexivity.
Qed.

End c.
End b.
End a.

(* ---- THE GENERIC WALK (an internal work row, the ARx drain walk DR_x; the image-B twin of lib/A/W_drain_top.v's generic Section
   c, a working branch d80aca9181b).  Section cxd states the head's cuts DT1_x / DSC_x and its stage
   statements over any allocator relation ARx in lib/B/W_drain_cx_x.v's forms (the entry's ghost list Hp and budget kr
   after cx, the cut's ghost list Hp1 an existential after S1, DMEM_x / dbud_x in place of DMEM / dbud, DBASE, DI, DT2
   and the post in their _x forms), and composes them as Section c composes the AR ones: dr_tophead_of_x,
   dt_scan_of_x and dr_top_of_x (dr_top_stmt_x from the head and W_drain_topb_cx.v's dr_toptail_stmt_x).  The AR
   texts above are unchanged; they are compiled before the Requires below, so no name of the generic kit is in scope
   in them (W_drain_topb_cx.v, which they Require, loads the kit without Importing it, and its own global zify line
   keeps the flag false). ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the zify flag this file's AR text runs with (false: W_drain_topb_cx.v's setting, the last its Requires leave), whatever
   the Requires above leave *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cxd.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation DBASEx := (DBASE_x B ARx MT RP MMAX RG).
#[local] Abbreviation DIx := (DI_x B PST ARx MT RP MMAX RG).
#[local] Abbreviation DT2x := (DT2_x B PST ARx MT RP MMAX RG).
#[local] Abbreviation dPOSTx := (dPOST_x B PST ARx MT RP RG).

(* The carriers of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, and every carrier or spec it names -> its R twin;
   every other token is the strict text's. The strict <name> is <name>R at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
#[local] Abbreviation DIxR := (DI_xR B PST ARx MT RP MMAX RG R).
#[local] Abbreviation DT2xR := (DT2_xR B PST ARx MT RP MMAX RG R).
#[local] Abbreviation dPOSTxR := (dPOST_xR B PST ARx MT RP RG R).

Definition DT1_xR (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_mid) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud_x B MT RP MMAX cx kr ly1 S1 spent tl.

Definition dt_nogrow_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASEx cx Hp kr -> DIxR cx Hp kr s1 D W1 c1 ->
4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
(forall W2 c2, DT1_xR cx Hp kr (dgrow s1) D W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).

Definition dt_grow_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASEx cx Hp kr -> DIxR cx Hp kr s1 D W1 c1 ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
(forall W2 c2, DT1_xR cx Hp kr (dgrow s1) D W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).

Definition dt_scan_stmt_xR : Prop :=
forall cx Hp kr sg D W1 c1,
DBASEx cx Hp kr -> DT1_xR cx Hp kr sg D W1 c1 ->
(forall W2 c2, DT2xR cx Hp kr sg D W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).

Definition dr_tophead_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASEx cx Hp kr -> DIxR cx Hp kr s1 D W1 c1 ->
(forall W2 c2, DT2xR cx Hp kr (dgrow s1) D W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).

Definition DSC_xR (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_scan) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
getr regs1 14 = w64 (re_fd e1) /\ getr regs1 12 = w64 (96 * Z.of_nat i) /\
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat i) /\
(i <= dxj cx)%nat /\
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud_x B MT RP MMAX cx kr ly1 S1 spent tl.

Definition dt_scan_entry_stmt_xR : Prop :=
forall cx Hp kr sg D W1 c1,
DBASEx cx Hp kr -> DT1_xR cx Hp kr sg D W1 c1 ->
(forall W2 c2, DSC_xR cx Hp kr sg D 0 W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).

Definition dt_scan_step_stmt_xR : Prop :=
forall cx Hp kr sg D i W1 c1,
DBASEx cx Hp kr -> DSC_xR cx Hp kr sg D i W1 c1 ->
(forall W2 c2, DSC_xR cx Hp kr sg D (S i) W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
(forall W2 c2, DT2xR cx Hp kr sg D W2 c2 -> SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).
End wR.

Definition DT1_x (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
DT1_xR (@wle SEGS) cx Hp kr sg D W1 c1.

Definition dt_nogrow_stmt_x : Prop :=
dt_nogrow_stmt_xR (@wle SEGS).

Definition dt_grow_stmt_x : Prop :=
dt_grow_stmt_xR (@wle SEGS).

Definition dt_scan_stmt_x : Prop :=
dt_scan_stmt_xR (@wle SEGS).

Definition dr_tophead_stmt_x : Prop :=
dr_tophead_stmt_xR (@wle SEGS).

Definition DSC_x (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (i : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
DSC_xR (@wle SEGS) cx Hp kr sg D i W1 c1.

Definition dt_scan_entry_stmt_x : Prop :=
dt_scan_entry_stmt_xR (@wle SEGS).

Definition dt_scan_step_stmt_x : Prop :=
dt_scan_step_stmt_xR (@wle SEGS).

(* ---- route R: the R twins of this Section's compositions over its R carriers (DT1_xR, DSC_xR and the stage
   statements at R).  The strict lemmas below are these twins at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
#[local] Abbreviation DIxR := (DI_xR B PST ARx MT RP MMAX RG R).
#[local] Abbreviation DT2xR := (DT2_xR B PST ARx MT RP MMAX RG R).
#[local] Abbreviation dPOSTxR := (dPOST_xR B PST ARx MT RP RG R).

Theorem dr_tophead_of_xR : dt_nogrow_stmt_xR R -> dt_grow_stmt_xR R -> dt_scan_stmt_xR R -> dr_tophead_stmt_xR R.
Proof.
intros NG GR SC cx Hp kr s1 D W1 c1 HB HDI K.
assert (KT1 : forall W2 c2, DT1_xR R cx Hp kr (dgrow s1) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr))
  by (intros W2 c2 H2; exact (SC cx Hp kr (dgrow s1) D W2 c2 HB H2 K)).
destruct (Z_le_gt_dec 4096 (drain_b_c.ds_cap s1 - ulen s1)) as [Hge|Hlt].
- exact (NG cx Hp kr s1 D W1 c1 HB HDI Hge KT1).
- exact (GR cx Hp kr s1 D W1 c1 HB HDI ltac:(lia) KT1).
Qed.

Theorem dr_top_of_xR : dr_tophead_stmt_xR R -> dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R ->
dr_top_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros HEAD TAIL cx Hp kr s1 D W1 c1 HB HI KE KD KR.
apply (HEAD cx Hp kr s1 D W1 c1 HB HI). intros W2 c2 H2.
exact (TAIL cx Hp kr (dgrow s1) D W2 c2 HB H2 KE KD KR).
Qed.

Lemma dt_DSC_le_xR : forall cx Hp kr sg D i W1 c1, DSC_xR R cx Hp kr sg D i W1 c1 -> (i <= dxj cx)%nat.
Proof.
intros cx Hp kr sg D i W1 c1
  (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
   _ & _ & _ & _ & _ & _ & _ & Hle & _).
exact Hle.
Qed.

Lemma dt_scan_loop_xR : forall n cx Hp kr sg D i W1 c1,
(4 - i <= n)%nat -> dt_scan_step_stmt_xR R -> DBASEx cx Hp kr -> DSC_xR R cx Hp kr sg D i W1 c1 ->
(forall W2 c2, DT2xR cx Hp kr sg D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOSTxR cx Hp kr)) ->
YA0nH.SRrG SEGS R W1 c1 (dPOSTxR cx Hp kr).
Proof.
induction n as [|n IH]; intros cx Hp kr sg D i W1 c1 Hn STEP HB HD K.
- assert (Hi : (i <= dxj cx)%nat) by exact (dt_DSC_le_xR cx Hp kr sg D i W1 c1 HD).
  assert (Hj : (dxj cx < 4)%nat)
    by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _); exact Hj).
  exfalso. clear - Hn Hi Hj. lia.
- apply (STEP cx Hp kr sg D i W1 c1 HB HD); [|exact K].
  intros W2 c2 H2. apply (IH cx Hp kr sg D (S i) W2 c2); [|exact STEP|exact HB|exact H2|exact K].
  assert (Hi : (S i <= dxj cx)%nat) by exact (dt_DSC_le_xR cx Hp kr sg D (S i) W2 c2 H2).
  assert (Hj : (dxj cx < 4)%nat)
    by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _); exact Hj).
  clear - Hn Hi Hj. lia.
Qed.

Theorem dt_scan_of_xR : dt_scan_entry_stmt_xR R -> dt_scan_step_stmt_xR R -> dt_scan_stmt_xR R.
Proof.
intros ENTRY STEP cx Hp kr sg D W1 c1 HB HD1 K.
apply (ENTRY cx Hp kr sg D W1 c1 HB HD1). intros W2 c2 H2.
exact (dt_scan_loop_xR 4 cx Hp kr sg D 0 W2 c2 ltac:(lia) STEP HB H2 K).
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R; the statements are the strict ones, checked by conversion). ---- *)
Theorem dr_tophead_of_x : dt_nogrow_stmt_x -> dt_grow_stmt_x -> dt_scan_stmt_x -> dr_tophead_stmt_x.
Proof. exact (dr_tophead_of_xR (@wle SEGS)). Qed.

Theorem dr_top_of_x : dr_tophead_stmt_x -> dr_toptail_stmt_x B PST ARx MT RP MMAX RG ->
dr_top_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dr_top_of_xR (@wle SEGS)). Qed.

Lemma dt_DSC_le_x : forall cx Hp kr sg D i W1 c1, DSC_x cx Hp kr sg D i W1 c1 -> (i <= dxj cx)%nat.
Proof. exact (dt_DSC_le_xR (@wle SEGS)). Qed.

Lemma dt_scan_loop_x : forall n cx Hp kr sg D i W1 c1,
(4 - i <= n)%nat -> dt_scan_step_stmt_x -> DBASEx cx Hp kr -> DSC_x cx Hp kr sg D i W1 c1 ->
(forall W2 c2, DT2x cx Hp kr sg D W2 c2 -> SRr SEGS W2 c2 (dPOSTx cx Hp kr)) ->
SRr SEGS W1 c1 (dPOSTx cx Hp kr).
Proof. exact (dt_scan_loop_xR (@wle SEGS)). Qed.

Theorem dt_scan_of_x : dt_scan_entry_stmt_x -> dt_scan_step_stmt_x -> dt_scan_stmt_x.
Proof. exact (dt_scan_of_xR (@wle SEGS)). Qed.

End cxd.
End b.
End a.

(* ---- THE GENERIC HEAD (an internal work row): dt_nogrow_x : dt_nogrow_stmt_x and dt_grow_x : dt_grow_stmt_x (Section cxd's
   statements), the image-B twins of lib/A/W_drain_top.v's generic dt_nogrow / dt_grow (a working branch
   d80aca9181b), proved over any allocator relation ARx with its laws at the room parameter RP, under W_drain_cx_x.v
   Section c's hypotheses that Section c above has a twin of, plus HP0 (no hidden head in any ARx state, the ruling of
   drx-a7-texts.md (sha256 a00dd49ffabb; internal record)): the entry's ghost list Hp and every cut's Hp1 are [], so every cut of the walk is read at Hp = [].
   Realloc #1 (0x83410, return 0x83414 = AF_fr_drain + 0x19c) is the caller-context rule arealloc_cf_rule_c_x at
   HCTX_re1: it takes its room rp_RM RP S1 (2 + kr') and its count premise from the cut's dbud_x, and DT1_x gets them
   back at the trace after the growth (dt_grow_room_rk_x, dt_grow_cnt_x).  The lemmas of Section c that read AR are
   restated here with the suffix _x; the AR-free ones are Section c's, cited with the Section arguments they took.
   The journal's stack budget is W_contract_x.v's DRAIN_STK_x (DRAIN_STK + 128 = 17008), as in DBASE_x and DMEM_x.
   The AR text above is unchanged. ---- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cxh.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* W_drain_cx_x.v Section c's hypotheses that Section c above has a twin of, word for word *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
(* drx-a7-texts.md (sha256 a00dd49ffabb; internal record) HP0: no hidden head in any ARx state *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].

(* Section c's local notations and tactics (gone after its End), restated *)
#[local] Abbreviation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 35 0)).
#[local] Abbreviation dt_gv c := (SAlu ALU_SRL (SOff 8 c) (SLit 3)).
#[local] Abbreviation BxT := (SOff 35 0).
Local Ltac dt_reg_x HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E (setpc ?ss ?pc) (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E (setpc ss pc) ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs (setpc ss pc)) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
Local Ltac dt_cs_x := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* the walk at the empty ghost list (HP0): every cut's ARx state, journal and memory core at Hp = [] *)
#[local] Abbreviation AR0 ly S W mem md := (ARx ly S [] W mem md).
#[local] Abbreviation DMEM0 cx ly S W m md k e h s out ev sent LB :=
  (DMEM_x B PST ARx RG cx [] ly S [] W m md k e h s out ev sent LB).
#[local] Abbreviation dbud0 cx := (dbud_x B MT RP MMAX cx).
#[local] Abbreviation AJ0 cx ly S W m md k :=
  (@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx) (dxmd cx) [] ly S [] W m md k).
#[local] Abbreviation DT1x := (DT1_x B PST ARx MT RP MMAX RG).
(* the entry's ghost list Hp is [] (HP0 at DBASE_x's afn_pre_x state) *)
Local Ltac dt_hp0_x HB Hp := let E := fresh "EHp" in
  assert (E : Hp = []) by (destruct HB as ((HAR & _) & _); exact (HP0 _ _ _ _ _ _ HAR)); subst Hp.

Lemma dt_shent_sub_x : forall ly S (W : world SEGS) mem md E (m : nat) p n q lo hi,
AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m p n q lo hi HAR Hin HB Hm H1 H2 H3.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
destruct (alx_shadow _ _ _ LAWS ly S [] W mem md p n HAR Hin (fun h (Hh : In h []) => match Hh with end))
  as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma dt_no_dup_block_x : forall ly S Hp (W : world SEGS) mem md x l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: x :: l) -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md x l HAR HP Hn.
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md x x l HAR HP) as Hd.
pose proof (req_size_pos (snd x) Hn) as (Hr & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma dt_buf_fp_x : forall cx ly1 S1 Hp1 (W1 : world SEGS) m1 md1 bl p n,
ARx ly1 S1 Hp1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: bl ++ dxrest cx) -> In (p, n) bl ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++
     dxrest cx) ->
In (p, n) (ablocks B (dxly cx) (dxS cx)) -> 0 <= n -> n <> ATABLE ->
forall i, 0 <= i < req_size n -> inFP (dFP cx) (p + i).
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 bl p n HAR HPc Hbl HP0' Hin0 Hn Hnt i Hi.
unfold dFP, dr_fp.
assert (Hin : In (p, n) ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx)) by (eapply Permutation_in; [exact HP0' | exact Hin0]).
destruct Hin as [Heq | Hin]; [injection Heq as _ Heq; congruence|].
apply in_app_or in Hin as [Hin | Hin]; [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_introl Hin)) Hi)|].
apply in_app_or in Hin as [Hin | Hin];
  [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hin)))) Hi)|].
apply in_app_or in Hin as [Hin | Hrest];
  [exact ((dt_inFP_of_blocks RG) _ p n i _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hin)))) Hi)|].
exfalso.
destruct (in_split _ _ Hbl) as (b1 & b2 & Eb).
destruct (in_split _ _ Hrest) as (d1 & d2 & Ed).
apply (dt_no_dup_block_x ly1 S1 Hp1 W1 m1 md1 (p, n) ((dxG cx, ATABLE) :: b1 ++ b2 ++ d1 ++ d2)); [exact HAR | | exact Hn].
eapply Permutation_trans; [exact HPc|].
rewrite Eb, Ed, <- !app_assoc.
apply Permutation_sym.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: b1) (l2 := b2 ++ d1 ++ (p, n) :: d2).
cbn [app]. rewrite !app_assoc.
apply Permutation_cons_app with (l1 := (dxG cx, ATABLE) :: (b1 ++ b2) ++ d1) (l2 := d2).
apply Permutation_refl.
Qed.

Lemma dt_sep_head_x : forall ly S Hp (W : world SEGS) m md x L y,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* ---- The room round at realloc #1 (W_drain_cx_x.v dbud_x): the request's room and its counts. ----
   MT_rk charges every request of a trace (a malloc and a realloc alike: mo_malloc + mo_free = 2, a free 1), so the
   growth's one request costs 2 and what the rest of the walk owes is the tail's charge; the counts move by the
   request's own net count (the new block in place of the old one), which the peak of the trace it opens covers
   (ReplyCnt.tr_peakP, the new block counted before the old one goes). *)
Lemma dt_tr_cost_app_g_x : forall (M : ameter_ops) (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
tr_cost M (t1 ++ t2) = tr_cost M t1 + tr_cost M t2.
Proof.
intros M t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
Lemma dt_tr_cost_rk_nonneg_x : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_cost MT_rk t.
Proof.
intros t. induction t as [|ev t IH]; [exact (Z.le_refl 0)|].
change (ev :: t) with ([ev] ++ t). rewrite dt_tr_cost_app_g_x.
assert (Hev : 0 <= tr_cost MT_rk [ev]) by (destruct ev; vm_compute; discriminate).
lia.
Qed.
Lemma dt_grow_rk_x : forall cap used j b, cap - used < 4096 ->
tr_cost MT_rk (fst (drain_b_c.grow_tr cap used j b)) = 2.
Proof.
intros cap used j b Hlt. unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt).
cbn [fst]. destruct (cap =? 0); reflexivity.
Qed.
(* the room the request needs, out of the cut's: 2 for the request, the tail's charge on top of kr after it *)
Lemma dt_grow_room_rk_x : forall S cap used j b (t : list (RelayRunT.rev YO0i.sptr)) (kr : nat), cap - used < 4096 ->
rp_RM RP S (Z.to_nat (tr_cost MT_rk (fst (drain_b_c.grow_tr cap used j b) ++ t)) + kr) ->
rp_RM RP S (2 + (Z.to_nat (tr_cost MT_rk t) + kr)).
Proof.
intros S cap used j b t kr Hlt H.
rewrite dt_tr_cost_app_g_x, (dt_grow_rk_x cap used j b Hlt) in H.
pose proof (dt_tr_cost_rk_nonneg_x t) as Ht.
replace (2 + (Z.to_nat (tr_cost MT_rk t) + kr))%nat with (Z.to_nat (2 + tr_cost MT_rk t) + kr)%nat by lia.
exact H.
Qed.
(* the counts after the request: at most the cut's, with the request's peak spent *)
Lemma dt_grow_cnt_x : forall ly1 S1 ly2 S2 buf cap nc res used j b (t : list (RelayRunT.rev YO0i.sptr)) P,
cap - used < 4096 -> nc = (if cap =? 0 then 8192 else cap * 2) ->
(cap = 0 -> buf = 0) -> (cap <> 0 -> buf <> 0) ->
(buf = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(buf <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (buf, cap) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) + ReplyCnt.tr_peakP P t <=
Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + ReplyCnt.tr_peakP P (fst (drain_b_c.grow_tr cap used j b) ++ t).
Proof.
intros ly1 S1 ly2 S2 buf cap nc res used j b t P Hlt Enc Hz Hnz HA HB'.
unfold drain_b_c.grow_tr. rewrite (proj2 (Z.ltb_lt (cap - used) 4096) Hlt). cbn [fst app].
pose proof (ReplyCnt.tr_peakP_nonneg _ P t) as Ht.
destruct (Z.eqb_spec cap 0) as [E|E]; cbn [ReplyCnt.tr_peakP]; subst nc.
- rewrite (ReplyCnt.acnt_perm P _ _ (HA (Hz E))), acnt_cons. cbn [snd]. unfold ReplyCnt.zb.
  destruct (P 8192); lia.
- destruct (HB' (Hnz E)) as (l1 & l2 & E1 & P2).
  rewrite (ReplyCnt.acnt_perm P _ _ P2), acnt_cons, E1, !ReplyCnt.acnt_app, acnt_cons. cbn [snd].
  unfold ReplyCnt.zb. destruct (P (cap * 2)), (P cap); lia.
Qed.

(* ---- route R: the R twins of the head's walks (dt_nogrow_xR, dt_grow_xR) and of the lemmas whose statements carry
   the journal, DMEM_x or DT1_x, over the R carriers; the runs are the G runs (paj_run_x_xG), the branch paj_branch_xR.
   Realloc #1 is the R rule AREALLOC_R, which also takes the call-boundary premises RO / HA at the call state: RO_ARx
   gives the first from the journal's ARx, HA_call the second from the meter.  The strict lemmas below are these twins
   at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

#[local] Abbreviation DMEM0R cx ly S W m md k e h s out ev sent LB :=
  (DMEM_xR B PST ARx RG R cx [] ly S [] W m md k e h s out ev sent LB).
#[local] Abbreviation AJ0R cx ly S W m md k :=
  (@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx) (dxmd cx) [] ly S [] W m md k).
#[local] Abbreviation DT1xR := (DT1_xR B PST ARx MT RP MMAX RG R).
Local Ltac dt_hp1_xR H Hp1 := let E := fresh "EHp" in
  assert (E : Hp1 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact (proj1 H)); subst Hp1.

Lemma dt_DMEM_kept_xR : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
AJ0R cx ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM0R cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 &
    A17 & A18 & A19 & A20 & A21 & A22 & A23 & ASV).
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (ASV i Hi) ]. }
split; [exact (dt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => Hkept x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact ((dt_aentry_okx_kept B RG) ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  ((dt_aentry_blks_in B RG HGSB) ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  ((dt_asrc_blks_in B RG HGSB) ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact ((dt_aout_blks_in B RG HGSB) ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

Theorem dt_nogrow_xR : dt_nogrow_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr s1 D W1 c1 HB HDI Hge K.
dt_hp0_x HB Hp.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
dt_hp1_xR HMEM Hp1.
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (Heof & Hskipv & Hpad1 & Hpad2 & Hfdv & Hcapv & HUlen & Hucap & Hbufc & Hnheld & Hheldc &
  HND1 & HND2 & Hkeys).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= 16384) by lia.
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen1 : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUlen).
assert (Hcappos : 0 < re_cap e1).
{ pose proof Hge as Hg'. rewrite <- Lcap, Hulen1 in Hg'.
  pose proof (Nat2Z.is_nonneg (length (re_U e1))). lia. }
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_ng_extra (dxSA cx) (re_cap e1) (re_used e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_ng
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ng. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_ng_frame, dt_ng_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      pose proof HFR as (G8 & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G88 & G104 & G120 & G128 & G136 &
        G144 & G152 & G176 & G184 & G200 & G208 & G216 & G224 & G232 & G240 & Gsaved).
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia); zside])
          | zside
          | exact G216 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 24 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia); zside])
          | zside
          | exact G232 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_used RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_cap RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_ng_frame, dt_ng_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_ng_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUNG BRR HS SHOK DBspan.
- paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_mid.
  { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  rewrite wvb_collapse in HJ.
  assert (Hnw : forall x, ~ in_wrange E (ss_mem ss_ng) x).
  { intros x (r & Hin & Hr). cbv [ss_mem ss_ng dt_ng_frame dt_ng_sa] in Hin.
    destruct Hin as [Hq|[Hq|[]]]; subst r;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
  { intros a.
    rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (Hnw _))).
    exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (Hnw _))). }
  assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
  dt_reg_x HS (2%bv : bv 5) X2. dt_reg_x HS (3%bv : bv 5) X3. dt_reg_x HS (4%bv : bv 5) X4.
  dt_reg_x HS (8%bv : bv 5) X8. dt_reg_x HS (9%bv : bv 5) X9. dt_reg_x HS (18%bv : bv 5) X18.
  dt_reg_x HS (20%bv : bv 5) X20. dt_reg_x HS (21%bv : bv 5) X21. dt_reg_x HS (22%bv : bv 5) X22.
  dt_reg_x HS (24%bv : bv 5) X24. dt_reg_x HS (26%bv : bv 5) X26. dt_reg_x HS (27%bv : bv 5) X27.
  pmkst HS.
  apply K. rewrite (dgrow_id s1 Hge). unfold DT1_xR.
  eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
    split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
    split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
    split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
    split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
    split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
           |rewrite X26; exact (eq_trans (eq_sym R26') R26)]. }
  split; [exact (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 s1 out1 ev1
    (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split; [apply Hband; lia|].
  split; [exact HLINK|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hge|].
  split; [exact Hlater | exact Hbud].
- rewrite ((dt_bnez_room RG HGSB) E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_gt in Hc.
  pose proof Hge as Hg2. rewrite <- Lcap, Hulen1 in Hg2. lia.
Qed.

Lemma dt_gx_open_xR : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.

Lemma dt_gx_close_xR : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

Lemma dt_grow_core_xR : forall cx kr s1 (W1 : world SEGS) ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1
  (W2 : world SEGS) ly2 S2 mem2 md2 m3 md3 res nc,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1 ->
DLINK s1 e1 h1 -> re_used e1 <= APARTIAL ->
drain_b_c.ds_cap (dgrow s1) = nc ->
nc = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) -> 8192 <= nc <= 16384 ->
AR0 ly2 S2 W2 mem2 md2 -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) nc ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
AJ0R cx ly2 S2 W2 m3 md3 (k1 + 3) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W2) mem2 x) ->
(forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m3 x) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 16) 8 res ->
val_mem SEGS (arm W2 m3) (dxSA cx + 32) 8 nc ->
exists junk,
  DMEM0R cx ly2 S2 W2 m3 md3 (k1 + 3) (dt_ge e1 res nc junk) h1 (dgrow s1) out1 ev1 sent LB1 /\
  DLINK (dgrow s1) (dt_ge e1 res nc junk) h1.
Proof.
intros cx kr s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1 W2 ly2 S2 mem2 md2 m3 md3 res nc
  HB HMEM HLINK Hused Enc Hncap Hnb HAR2 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ3 KV KP V16 V32.
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
pose proof HMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT &
  HLIVE & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (FB : alloc_ceiling + DRAIN_STK_x <= dsp0 cx /\ dsp0 cx <= 2 ^ 47)
  by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
assert (AR1 : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (AR3 : AR0 ly2 S2 W2 m3 md3) by (eapply ajournal_gx_AR_xR; exact HJ3).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HU & Hucap & HBUF & _ & HHP & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (HSAle' : dxSA cx + 56 <= dxG cx + 896) by (clear - HSAle; unfold AENT, ATABLE in HSAle; lia).
assert (Hcn : re_cap e1 <= nc /\ (nc = 8192 \/ nc = 16384)).
{ clear - Hncap Hnb Hcapv. destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in Hncap; cbn [Z.eqb] in Hncap; lia. }
assert (RQN : req_size nc = nc) by (unfold req_size; destruct (Z.eqb_spec nc 0) as [E0|E0]; [lia | reflexivity]).
(* ---- the live blocks before and after the call ---- *)
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> 4096 <= re_buf e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (alx_blocks SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 _ _ AR1 Hin) as (_ & H4 & _). split; [exact H4 | exact Hin]. }
assert (Hnz' : re_cap e1 <> 0 -> re_buf e1 <> 0) by (intros Hc; destruct (Hnz Hc) as (H4 & _); lia).
pose proof ((dt_grow_perm B) ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res nc HPERM Hz Hnz' HpermA HpermB)
  as P2.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, nc)).
pose (Rl := asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
pose (Q := dt_hkb e1 ++ Rl).
change (Permutation (ablocks B ly2 S2) (NB :: TB :: Q)) in P2.
assert (P2T : Permutation (ablocks B ly2 S2) (TB :: NB :: Q))
  by (eapply Permutation_trans; [exact P2 | apply perm_swap]).
assert (P1 : Permutation (ablocks B ly1 S1) (TB :: (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ Q)).
{ eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
  change (aentry_blks e1) with ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ dt_hkb e1).
  rewrite <- app_assoc. apply Permutation_refl. }
assert (Q1 : forall b, In b (TB :: Q) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). destruct Hb as [<-|Hb]; [left; reflexivity|].
  right. apply in_or_app. right. exact Hb. }
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2T)); left; reflexivity).
assert (Q2 : forall b, In b Q -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P2)); right; right; exact Hb).
assert (DNB : forall b, In b (TB :: Q) -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head_x ly2 S2 [] W2 mem2 md2 NB (TB :: Q) b HAR2 P2 Hb)).
assert (DOB : re_cap e1 <> 0 -> forall b, In b (TB :: Q) ->
  zdisjoint (block_rng (re_buf e1, re_cap e1)) (block_rng b)).
{ intros Hc b Hb. apply (dt_sep_head_x ly1 S1 [] W1 m1 md1 _ (TB :: Q) b AR1); [|exact Hb].
  eapply Permutation_trans; [exact P1|]. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [app]. apply perm_swap. }
assert (DTQ : forall b, In b Q -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (dt_sep_head_x ly2 S2 [] W2 mem2 md2 TB (NB :: Q) b HAR2 P2T (or_intror Hb))).
destruct (alx_blocks SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE AR1 (Q1 TB (or_introl eq_refl)))
  as (_ & HG4096 & HGceil & _).
rewrite RQT in HGceil.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 res nc AR3 NB2) as (_ & HN4 & HNcl & _ & HNpr & _).
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 (dxG cx) ATABLE AR3 TB2) as (_ & _ & _ & _ & HTpr & _).
rewrite RQN in HNcl, HNpr. rewrite RQT in HTpr.
(* ---- what the call keeps of the table and the entry's other blocks ---- *)
assert (KC : forall b x, In b (TB :: Q) -> fst b <= x < fst b + req_size (snd b) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) m1 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. pose proof Hkept2 as (_ & K2 & _).
  replace x with (pb + (x - pb)) by ring. apply (K2 pb mb (x - pb) (Q1 _ Hb)); [lia|].
  replace (pb + (x - pb)) with x by ring. cbv beta.
  intros [Hn | (Hb0 & Ho)].
  - pose proof (DNB _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj. lia.
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    pose proof (DOB Hc _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj. lia. }
(* ---- and what the stores keep ---- *)
assert (KO : forall b x, In b Q -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m3 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx.
  pose proof (DTQ _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj. rewrite RQT in Dj.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 [] W2 m3 md3 pb mb AR3 (Q2 _ Hb)) as (_ & H4 & Hcl & _ & Hpr & _).
  assert (Hr : 0 <= x < 2 ^ 64) by lia.
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x Hr N1 N2). exact (KC (pb, mb) x (or_intror Hb) Hx).
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (FK : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64)
    by (clear - Hx FB HAC; unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, DRAIN_FRAME, ASTACK in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  assert (N1 : ~ (dxSA cx + 16 <= x < dxSA cx + 24)) by lia.
  assert (N2 : ~ (dxSA cx + 32 <= x < dxSA cx + 40)) by lia.
  split.
  - rewrite (KV x ltac:(lia) N1 N2). exact (K1 x Hr1 Hr2).
  - intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
    intros Hp. apply KP. exact (K5 x Hr1 Hr2 Hp). }
assert (NIMG : forall x, in_img SEGS x ->
  ~ (dxSA cx + 16 <= x < dxSA cx + 24) /\ ~ (dxSA cx + 32 <= x < dxSA cx + 40)).
{ intros x Hx. split; intros Hw;
    exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE x AR1 (Q1 TB (or_introl eq_refl))
      ltac:(rewrite RQT; lia) Hx). }
assert (APK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m3 x).
{ intros x Hi Hno Herr Hp.
  assert (Hnot : forall ly0 S0 (W0 : world SEGS) m0 md0, AR0 ly0 S0 W0 m0 md0 -> ~ aowned B ly0 S0 x)
    by (intros ly0 S0 W0 m0 md0 HAl Ho; apply Hno; exact (proj1 (alx_owned_image SEGS B ARx LAWS ly0 S0 [] W0 m0 md0 x HAl Hi) Ho)).
  apply KP. apply (Hpres2 x Hi (Hnot _ _ _ _ _ AR1) (Hnot _ _ _ _ _ HAR2) Herr); [|exact Hp].
  intros [Hn | (Hb0 & Ho)].
  - exact (blk_img_x SEGS B ARx LAWS ly2 S2 [] W2 mem2 md2 res nc x HAR2 NB2 Hn Hi).
  - assert (Hc : re_cap e1 <> 0) by (intros Hc; apply Hb0; exact (Hz Hc)).
    exact (blk_img_x SEGS B ARx LAWS ly1 S1 [] W1 m1 md1 (re_buf e1) (re_cap e1) x AR1 (proj2 (Hnz Hc)) Ho Hi). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  assert (Hi : in_img SEGS x) by exact (proj1 (HG x Hg)).
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  assert (EV : aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KV x Hr N1 N2). replace x with (as_errno B + (x - as_errno B)) by ring. apply Herr2.
    clear - Hx; lia. }
  split; [exact EV|]. intros _.
  apply (dt_img_wr RG); [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m3 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [destruct (HG x Hx) as (Gi & Gn & _) | destruct (HGO x Hx) as (Gi & Gn & _)]; exact (conj Gi Gn)).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by lia.
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  destruct (NIMG x Hi) as (N1 & N2).
  assert (Hr : 0 <= x < 2 ^ 64)
    by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
  pose proof Hkept2 as (_ & _ & K3 & _).
  split; [rewrite (KV x Hr N1 N2); exact (K3 x Hi Ho Hne)|].
  intros Hw. apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 m3 x); [|exact Hw].
  intros Hp. exact (APK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m3 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
assert (TK : forall x, dxSA cx <= x < dxSA cx + 56 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
  ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) m3 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx N1 N2. rewrite (KV x ltac:(lia) N1 N2).
  apply (KC TB x (or_introl eq_refl)). unfold TB. cbn [fst snd]. rewrite RQT. lia. }
(* ---- the entry: the new buffer, its bytes and the 56 bytes at SA ---- *)
assert (CP3 : 0 < re_cap e1 -> forall i, 0 <= i < re_cap e1 ->
  aview SEGS (w_H W2) m3 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)).
{ intros Hc i Hi.
  pose proof (DNB TB (or_introl eq_refl)) as Dj. unfold zdisjoint, block_rng, NB, TB in Dj. cbn [fst snd] in Dj.
  rewrite RQT, RQN in Dj.
  rewrite (KV (res + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Hcopy; [destruct (Hnz ltac:(lia)) as (H4 & _); lia | rewrite Z.min_l by lia; exact Hi]. }
assert (HBUF' : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (destruct HBUF as [Hq|(Hq1 & _ & Hq3 & Hq4)]; [left; exact Hq | right; exact (conj Hq1 (conj Hq3 Hq4))]).
assert (Hcb : 0 <= re_cap e1 <= nc) by (destruct Hcapv as [Hq|[Hq|Hq]]; lia).
destruct ((dt_newbuf RG HGSB) W1 m1 W2 m3 e1 res nc HBUF' HU Hcb CP3 (fun x Hx => proj1 (HNpr x Hx)))
  as (junk & Hjl & Hjg).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
assert (Hnc64 : 0 <= nc < 2 ^ 64) by lia.
assert (ENT3 : garr8 SEGS (arm W2 m3) (dxSA cx) (bzs (entry_bytes (dt_ge e1 res nc junk)))).
{ apply ((dt_entry_grow RG HGSB) W1 m1 W2 m3 (dxSA cx) e1 res nc junk Hp1 Hres64 Hnc64 HENTB V16 V32); [| | | exact Hp2];
    intros x Hx; apply TK; lia. }
assert (AWR3 : awr W2 m3 (dxSA cx) AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  apply (proj1 (HTpr (dxSA cx + i) ltac:(unfold AENT in Hi; lia))). }
assert (AK : akept W1 m1 W2 m3 (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e1))).
{ intros r Hr x Hx. destruct Hr as [<- | Hr].
  - unfold gfp in Hx. cbn [fst snd] in Hx. rewrite dt_bzs_len, (dt_key_ptrs_len RG) in Hx.
    destruct HHP as [(Hz0 & Hk0) | (Hz0 & HinH & Hk1 & Hk2 & _)].
    + rewrite Hk0 in Hx. cbn [length] in Hx. lia.
    + apply (KO (re_hp e1, re_kh e1) x).
      * unfold Q, dt_hkb. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz0).
        apply in_or_app. left. left. reflexivity.
      * cbn [fst snd]. unfold re_nheld in Hk1. pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & RQ). lia.
  - apply in_map_iff in Hr as (k & <- & Hk).
    apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
    + unfold Q, dt_hkb. apply in_or_app. left. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    + unfold gfp in Hx. cbn [fst snd] in Hx |- *. rewrite dt_bzs_len, length_app in Hx. cbn [length] in Hx.
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & RQ). lia. }
assert (OKX3 : aentry_okx B ly2 S2 W2 m3 (dt_ge e1 res nc junk)).
{ apply ((dt_aentry_okx_grow B RG) ly1 S1 W1 m1 ly2 S2 W2 m3 e1 res nc junk HOKX (proj2 Hcn)
    ltac:(unfold APARTIAL in Hused; lia) NB2 Hjl Hjg AK).
  intros b Hb. apply Q2. unfold Q. apply in_or_app. left. exact Hb. }
(* ---- the harness source, the other slots, g_s, the output ---- *)
assert (SRC3 : asrc_at B ly2 S2 W2 m3 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m3 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct ((dt_src_fp B RG HGSB) ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold Q, Rl. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - intros b Hb. apply Q2. unfold Q, Rl. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (OTH3 : aothers_at RG W2 m3 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & Va & Vb & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m3) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact Va] | split; [apply GV; [| | exact Vb] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK3 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m3 x)
  by (intros x H1 H2; exact (dt_bk_trans _ _ W1 m1 W2 m3 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT3 : aout_at B RG ly2 S2 W2 m3 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m3 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct ((dt_out_fp B RG) _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, drain_b_c.ds_ocap s1) x).
    + unfold Q, Rl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply Q2. unfold Q, Rl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (ROM3 : rom_view SEGS W2 m3).
{ intros x Hx. destruct (HROMO x Hx) as (_ & Hpin & Hne & _).
  destruct (Exists_dec (in_zr x) (as_owned_static B) ((dt_in_zr_dec RG) x)) as [Hown | Hno].
  - eapply (rom_pinned_view_x SEGS B ARx LAWS); [exact AR3 | exact (Hpin Hown)].
  - assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    destruct (NIMG x Hi) as (N1 & N2).
    assert (Hr : 0 <= x < 2 ^ 64)
      by (pose proof (pa_segs_low x Hi) as Hl; clear - Hl; unfold kLowMemEnd in Hl; lia).
    pose proof Hkept2 as (_ & _ & K3 & _).
    rewrite (KV x Hr N1 N2), (K3 x Hi Hno Hne). exact (HROM x Hx). }
assert (PK3 : apres_kept B (dxW cx) (dxmem cx) W2 m3)
  by (intros x Hi Ho He Hp; exact (APK x Hi Ho He (HPRESK x Hi Ho He Hp))).
assert (EA2 : aentry_blks (dt_ge e1 res nc junk) = NB :: dt_hkb e1).
{ unfold aentry_blks, dt_ge, dt_hkb. cbn [re_cap re_buf re_hp re_kh re_keys].
  rewrite (proj2 (Z.eqb_neq nc 0) ltac:(lia)). reflexivity. }
exists junk. split.
- unfold DMEM_xR.
  refine (conj HJ3 (conj ROM3 (conj PK3 (conj (eq_trans Hfrs2 HFRM) (conj ((dt_frame_kept RG HGSB) cx W1 m1 W2 m3 FK HFRAME)
    (conj ENT3 (conj AWR3 (conj OKX3 (conj SRC3 (conj OTH3 (conj GSK3 (conj OUT3 (conj HLIVE _))))))))))))).
  rewrite EA2. exact P2T.
- pose proof HLINK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  refine (conj (eq_sym Enc) (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10
    (conj K11 K12))))))))))).
Qed.

Lemma dt_grow_post_xR : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl
  memS (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 res tl2,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) ->
8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384 ->
tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)) ++ tl2 ->
dlater cx (dgrow s1)
  (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa))))
  (agrow s1 jb aa) tl2 ->
0 <= DRAIN_STK_x -> gagree (G_DR B RG) (w_H (dxW cx)) (dxmem cx) memS ->
ajournal_xR SEGS B PST ARx R DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) memS (dxmd cx) []
  ly2 S2 Hp2 W2 mem2 md2 (k1 + 3) ->
aregs_preserved regs1 regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2)
   ((res, drain_b_c.ds_cap (dgrow s1)) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, drain_b_c.ds_cap (dgrow s1)) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
            (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
mo_le MT S1 S2 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
      (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
(forall W3 c3, DT1xR cx [] kr (dgrow s1) D W3 c3 -> YA0nH.SRrG SEGS R W3 c3 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W2 (mkCfg (mkst regs2 (w64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)) md2) (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS W2 ly2 S2 Hp2 regs2 mem2 md2 res
  tl2   HB Hregs Hra R10 R11 R19
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2i HPR Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 HRM2 Herr2 Hpres2 K.
assert (EHp2 : Hp2 = []) by (eapply HP0; exact (proj1 HJ2i)). subst Hp2.
destruct Hbud as (Hbud & HRM1 & HCNT1).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR1 : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by exact (proj1 HJ2i).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR1 HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & Hcapv & HUl & Hucap & HBUF & _).
assert (Hz : re_cap e1 = 0 -> re_buf e1 = 0)
  by (intros Hc; destruct HBUF as [(_ & Hb & _)|(Hc' & _)]; [exact Hb | lia]).
assert (Hnz : re_cap e1 <> 0 -> re_buf e1 <> 0).
{ intros Hc. destruct HBUF as [(Hc' & _)|(_ & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & _). lia. }
pose proof ((dt_grow_perm B) ly1 S1 ly2 S2 (dxG cx, ATABLE)
  (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) e1 res (drain_b_c.ds_cap (dgrow s1))
  Hperm Hz Hnz HpermA HpermB) as HP2.
assert (TB2 : In (dxG cx, ATABLE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); right; left; reflexivity).
assert (NB2 : In (res, drain_b_c.ds_cap (dgrow s1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 _ _ HAR2 NB2) as (_ & _ & HNcl & _).
pose proof (req_size_pos (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)) as (_ & RQN).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 mem2 md2 (dxG cx) ATABLE HAR2 TB2) as (_ & _ & _ & _ & HTP2 & _).
assert (FK0 : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W2 mem2 x).
{ intros x Hx. pose proof Hkept2 as (K1 & _ & _ & _ & K5 & _).
  assert (Hr1 : alloc_ceiling <= x < 2 ^ 64) by (clear - Hx HspA HspB; unfold DRAIN_FRAME in *; lia).
  assert (Hr2 : ~ (dsp0 cx - DRAIN_FRAME - ASTACK <= x < dsp0 cx - DRAIN_FRAME)) by (clear - Hx; lia).
  split; [exact (K1 x Hr1 Hr2)|]. intros Hw.
  apply (dt_wr_kept2 (w_H W1) (w_H W2) m1 mem2 x); [|exact Hw]. exact (K5 x Hr1 Hr2). }
pose proof ((dt_frame_kept RG HGSB) cx W1 m1 W2 mem2 FK0 HFR) as HFR2.
pose proof HFR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F216' & F224' & _).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (P2 : getr regs2 2 = getr regs1 2) by (apply PR; dt_cs_x).
assert (P3 : getr regs2 3 = getr regs1 3) by (apply PR; dt_cs_x).
assert (P4 : getr regs2 4 = getr regs1 4) by (apply PR; dt_cs_x).
assert (P8 : getr regs2 8 = getr regs1 8) by (apply PR; dt_cs_x).
assert (P9 : getr regs2 9 = getr regs1 9) by (apply PR; dt_cs_x).
assert (P18 : getr regs2 18 = getr regs1 18) by (apply PR; dt_cs_x).
assert (P19 : getr regs2 19 = getr regs1 19) by (apply PR; dt_cs_x).
assert (P20 : getr regs2 20 = getr regs1 20) by (apply PR; dt_cs_x).
assert (P21 : getr regs2 21 = getr regs1 21) by (apply PR; dt_cs_x).
assert (P22 : getr regs2 22 = getr regs1 22) by (apply PR; dt_cs_x).
assert (P24 : getr regs2 24 = getr regs1 24) by (apply PR; dt_cs_x).
assert (P26 : getr regs2 26 = getr regs1 26) by (apply PR; dt_cs_x).
assert (P27 : getr regs2 27 = getr regs1 27) by (apply PR; dt_cs_x).
unfold w64.
remember (Eimg (Ereg regs2 (dt_gp_extra (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hr)).
assert (E2 : ew E 2 = getr regs2 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs2 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs2 4) by (apply EREG; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 res)
  by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact Hres10).
assert (E19 : ew E 19 = Z_to_bv 64 (drain_b_c.ds_cap (dgrow s1)))
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite P19; exact R19).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); rewrite P8; exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2, P2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (R21' : getr regs2 21 = sv_denot E (SOff 32 0))
  by (rewrite P21, (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs2 24 = sv_denot E (SOff 32 8))
  by (rewrite P24, (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs2 20 = sv_denot E (SOff 32 16))
  by (rewrite P20, (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs2 22 = sv_denot E (SOff 32 24))
  by (rewrite P22, (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs2 27 = sv_denot E (SOff 32 32))
  by (rewrite P27, (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs2 9 = sv_denot E (dt_gv 0))
  by (rewrite P9, ((dt_den_gv RG) E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs2 18 = sv_denot E (dt_gv 4))
  by (rewrite P18, ((dt_den_gv RG) E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs2 26 = sv_denot E (SLit 384))
  by (rewrite P26, denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_gp
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gp. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gp_frame, dt_gp_buf, dt_gp_cap;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia); zside])
          | zside | exact F216' ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 16 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia); zside])
          | zside | exact F224' ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (HTP2 (dxSA cx + o) ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia))).
  - apply pairwise_disjoint_of_extents. unfold dt_gp_frame, dt_gp_buf, dt_gp_cap, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gp_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W2) mem2)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly2 S2 W2 mem2 md2 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR2 TB2).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
pose proof (dt_gx_close_xR (G_DR B RG) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 [] W2 mem2 md2 (k1 + 3) memS HSTK HAG HJ2i) as HJ2.
psrr_branch_tok RUNG BRR HS SHOK DBspan.
- exfalso. rewrite ((dt_beqz_atom RG) E 10 res E10 Hres64) in Hc. apply Z.eqb_eq in Hc. lia.
- paj_run_to_tok_xR RUNTOG HS HJ2 SHOK DBspan A_dr_mid.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa0 Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_cons.
    { intros aa0 Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
      left. split; [|lia]. right; left. split.
      - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      - exists (dxG cx), ATABLE. split; [exact TB2|]. rewrite RQT. clear - Ha HGle HSAhi.
        unfold AENT, ATABLE in *. lia. }
    apply awr_ok_x_nil. }
  rewrite ?wvb_collapse in HJ2.
  assert (Hnw : forall x, ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
    ~ in_wrange E (ss_mem ss_gp) x).
  { intros x N1 N2 (r & Hin & Hr). cbv [ss_mem ss_gp dt_gp_frame dt_gp_buf dt_gp_cap] in Hin.
    destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?U32 in Hr; lia. }
  assert (KV : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) ->
    ~ (dxSA cx + 32 <= x < dxSA cx + 40) -> aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x)
    by (intros x Hx N1 N2; exact (aview_kept_out E _ (w_H W2) mem2 (ms_mem ms) HFr x Hx (Hnw x N1 N2))).
  assert (KP : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem ms) x)
    by (intros x Hx; exact (apresent_grows _ _ _ _ HG0 Hx)).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RB.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RC.
  cbn [ms_mem restrict] in RB, RC.
  assert (V16 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 16) 8 res).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 16 8%N (SOff 10 0) res RB U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 10 res E10 Hres64).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  assert (V32 : val_mem SEGS (arm W2 (ms_mem ms)) (dxSA cx + 32) 8 (drain_b_c.ds_cap (dgrow s1))).
  { refine (field_of_region E _ 32 (dxSA cx) _ _ _ _ _ 32 8%N (SOff 19 0) (drain_b_c.ds_cap (dgrow s1))
      RC U32 _ _ _ _).
    - cbn [In]. left. reflexivity.
    - exact (den_atom0 E 19 (drain_b_c.ds_cap (dgrow s1)) E19 ltac:(lia)).
    - change (8 * Z.of_N 8) with 64. lia.
    - cbn. lia. }
  dt_reg_x HS (2%bv : bv 5) X2. dt_reg_x HS (3%bv : bv 5) X3. dt_reg_x HS (4%bv : bv 5) X4.
  dt_reg_x HS (8%bv : bv 5) X8. dt_reg_x HS (9%bv : bv 5) X9. dt_reg_x HS (18%bv : bv 5) X18.
  dt_reg_x HS (20%bv : bv 5) X20. dt_reg_x HS (21%bv : bv 5) X21. dt_reg_x HS (22%bv : bv 5) X22.
  dt_reg_x HS (24%bv : bv 5) X24. dt_reg_x HS (26%bv : bv 5) X26. dt_reg_x HS (27%bv : bv 5) X27.
  pmkst HS.
  pose proof HLINK as (Lcap & Lu & Lrest).
  assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len; exact HUl).
  destruct ((dt_grow_ev MT RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
    ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
  change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
  assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
  { pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(lia)).
    pose proof (mo_free_nonneg MT MTL). lia. }
  assert (Hb0 : re_buf e1 = 0 -> re_cap e1 = 0)
    by (intros Hb; destruct (Z.eq_dec (re_cap e1) 0) as [Hq|Hq]; [exact Hq | exfalso; exact (Hnz Hq Hb)]).
  pose proof ((dt_grow_bbx B RG) ly1 S1 ly2 S2 e1 res (drain_b_c.ds_cap (dgrow s1)) Hb0 HpermA HpermB) as HBB.
  assert (HBB2 : blocks_bytes S2 + tr_peak tl2 <= LIVE_MAX).
  { pose proof Hbud as (_ & _ & _ & Hlv & _). rewrite Htl in Hlv.
    destruct ((dt_grow_pk RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
      ltac:(rewrite <- Lcap; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlv) as (_ & Hpk).
    change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hpk.
    rewrite <- Lcap in Hpk. lia. }
  pose proof ((dt_grow_bud MT MMAX RG MTL HGSB) cx S1 S2 spent tl tl2 _ (drain_b_c.ds_cap (dgrow s1)) Hbud Htl Hev_co Hev_max
    HmoN Hmle2 HBB2) as HBUD2.
  (* the room round: the counts after the request, at the tail's peak *)
  assert (HCNT2 : cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl2) + 2)%nat) (ablocks B ly2 S2)).
  { eapply (cnt_ok_pk_mono RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 2)%nat) _ (ablocks B ly1 S1) _);
      [|exact HCNT1].
    intros P. cbv beta.
    assert (Htl' : tl = fst (drain_b_c.grow_tr (re_cap e1) (re_used e1) jb (drain_b_c.da_buf aa)) ++ tl2)
      by (rewrite Lcap, <- Hulen; exact Htl).
    pose proof (dt_grow_cnt_x ly1 S1 ly2 S2 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) res (re_used e1) jb
      (drain_b_c.da_buf aa) tl2 P ltac:(rewrite Lcap, <- Hulen; exact Hlt) Hncap Hz Hnz HpermA HpermB) as Hcn.
    rewrite <- Htl' in Hcn.
    pose proof (ReplyCnt.tr_peakP_nonneg _ P tl2). pose proof (ReplyCnt.tr_peakP_nonneg _ P tl). lia. }
  destruct (dt_grow_core_xR cx kr s1 W1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 (lines (dSTR cx) D) LB1 W2 ly2 S2 mem2 md2
    (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1)) HB HMEM HLINK Hused eq_refl Hncap Hnb HAR2 Hfrs2 Hres4096
    HpermA HpermB Hcopy Hkept2 Herr2 Hpres2 HJ2 KV KP V16 V32) as (junk & HDM & HDL).
  apply K. unfold DT1_xR.
  eexists _, ly2, S2, [], _, _, (k1 + 3), (dt_ge e1 res (drain_b_c.ds_cap (dgrow s1)) junk), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)), _, (agrow s1 jb aa), tl2.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2), P2; exact Hsp|].
    split; [rewrite X3, (dt_den_reg E 3 _ E3), P3; exact R3|].
    split; [rewrite X4, (dt_den_reg E 4 _ E4), P4; exact R4|].
    split; [rewrite X21; exact (eq_trans (eq_sym R21') (eq_trans P21 R21))|].
    split; [rewrite X24; exact (eq_trans (eq_sym R24') (eq_trans P24 R24))|].
    split; [rewrite X20; exact (eq_trans (eq_sym R20') (eq_trans P20 R20))|].
    split; [rewrite X22; exact (eq_trans (eq_sym R22') (eq_trans P22 R22))|].
    split; [rewrite X27; exact (eq_trans (eq_sym R27') (eq_trans P27 R27))|].
    split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
    split; [rewrite X9; exact (eq_trans (eq_sym R9') (eq_trans P9 R9))|].
    split; [rewrite X18; exact (eq_trans (eq_sym R18') (eq_trans P18 R18))
           |rewrite X26; exact (eq_trans (eq_sym R26') (eq_trans P26 R26))]. }
  split; [exact HDM|].
  split; [exact HnoNUL|]. split; [exact Hused|].
  split; [unfold dinband, dt_ge; cbn [re_buf re_cap];
    pose proof YM05.alloc_ceiling_lt as HAC; unfold DCEIL;
    (split; [lia|]); (split; [lia|]); apply (Z.mod_divide res 8 ltac:(lia));
    destruct (alx_blocks _ _ _ LAWS ly2 S2 [] W2 (ms_mem ms) _ res (drain_b_c.ds_cap (dgrow s1))
      ltac:(eapply ajournal_gx_AR_xR; exact HJ2) NB2) as (Hm16 & _);
    apply Z.mod_divide in Hm16; [|lia]; destruct Hm16 as (q & ->); exists (2 * q); lia|].
  split; [exact HDL|]. split; [exact HSAME|].
  split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
  split; [exact Hlater2|]. split; [exact HBUD2|]. split; [exact HRM2 | exact HCNT2].
Qed.

Lemma dt_grow_after_xR : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM0R cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
(forall W2 c2, DT1xR cx [] kr (dgrow s1) D W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx [] kr)) ->
YA0nH.SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1) (dPOST_xR B PST ARx MT RP RG R cx [] kr).
Proof.
intros cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
  Hregs Hra R10 R11 R19 HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud0 K.
pose proof Hbud0 as (Hbud & HRM1 & HCNT1).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; clear - Hceil Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hcapv : re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); clear - Hq; lia).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (clear - Hcapv; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hroom : 4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1)).
{ apply (dt_grow_room RG HGSB); [exact Hlt | rewrite Hulen; clear - Hused Husedb; unfold APARTIAL in Hused |- *; lia
  | rewrite Hulen, <- Lcap; exact Hucap | rewrite <- Lcap; exact Hcapv ]. }
assert (Hncap : drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2)).
{ change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
  rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; exact Hucap) Hlt),
    <- Lcap. reflexivity. }
assert (Hnb : 8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384)
  by (rewrite Hncap; clear - Hcapv Hused Hucap Hlt Lcap Hulen; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq in *;
      cbn [Z.eqb]; [lia | lia | unfold APARTIAL in Hused; lia]).
destruct ((dt_grow_tr RG HGSB) cx s1 jb aa tl Hlater Hroom) as (tl2 & Htl & Hlater2).
(* the room the request needs (2 for it, the tail's charge on top of kr after it) *)
assert (HRMc : rp_RM RP S1 (2 + (Z.to_nat (tr_cost MT_rk tl2) + kr))).
{ pose proof HRM1 as H. rewrite Htl in H. exact (dt_grow_room_rk_x S1 _ _ _ _ tl2 kr Hlt H). }
assert (HDINV : dinv (dgrow s1)).
{ unfold dinv.
  change (drain_b_c.ds_ka (dgrow s1)) with (drain_b_c.ds_ka s1).
  change (drain_b_c.ds_ecap (dgrow s1)) with (drain_b_c.ds_ecap s1).
  change (drain_b_c.ds_ocap (dgrow s1)) with (drain_b_c.ds_ocap s1).
  change (drain_b_c.ds_no (dgrow s1)) with (drain_b_c.ds_no s1).
  pose proof HLINK as (_ & _ & _ & _ & Lka & _ & _ & _ & _ & _ & Lec & _).
  pose proof HHIST as (_ & _ & _ & _ & _ & Hno & _).
  destruct ((dt_aout_nn B RG) ly1 S1 W1 m1 _ _ _ _ _ _ Hout) as (_ & Hoc0 & _).
  pose proof ((dt_src_ecap B) ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc) as Hec.
  assert (Hka0 : 0 <= drain_b_c.ds_ka s1)
    by (rewrite <- Lka; unfold drain_b_c.ent_ka; destruct (re_hp e1 =? 0) eqn:Ehp; [lia|];
        pose proof ((dt_entry_kh B) ly1 S1 W1 m1 e1 HEOK Ehp) as Hk; clear - Hk; lia).
  assert (Hno1 : 0 <= drain_b_c.ds_no s1).
  { rewrite Hno. pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hout0 & _).
    destruct ((dt_aout_nn B RG) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) _ _ _ _ _ _ Hout0) as (Hn0 & _).
    clear - Hn0; lia. }
  split; [clear - Hnb; lia|]. split; [exact Hka0|].
  split; [rewrite <- Lec; exact Hec|]. split; [exact Hoc0 | exact Hno1]. }
destruct ((dt_later_meters MT RG MTL HGSB) cx (dgrow s1) _ _ tl2
  ltac:(destruct ((dt_aout_nn B RG) ly1 S1 W1 m1 _ _ _ _ _ _ Hout) as (_ & _ & Hmx); clear - Hmx; lia) HDINV Hlater2)
  as (Hal2 & Hco2).
destruct ((dt_grow_ev MT RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)
  ltac:(rewrite <- Lcap; clear - Hcapb; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt) as (Hev_max & _ & Hev_co).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hev_max, Hev_co.
pose proof Hbud as (Hmle & Hspent & Hcost & Hlive & Hmax).
rewrite Htl, (dt_tr_max_app RG HGSB), Hev_max in Hmax.
rewrite Htl in Hlive.
destruct ((dt_grow_pk RG HGSB) (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa) tl2 (blocks_bytes S1)
  ltac:(rewrite <- Lcap; clear - Hcapb; lia) ltac:(rewrite Hulen, <- Lcap; exact Hucap) Hlt Hlive) as (Hlv1 & _).
change (gcap (drain_b_c.ds_cap s1) (ulen s1)) with (drain_b_c.ds_cap (dgrow s1)) in Hlv1.
rewrite Htl, (dt_tr_cost_app MT RG), Hev_co in Hcost.
assert (HmoN : 0 <= mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT).
{ pose proof (mo_malloc_nonneg MT MTL (drain_b_c.ds_cap (dgrow s1)) ltac:(clear - Hnb; lia)) as M1.
  pose proof (mo_free_nonneg MT MTL) as M2. clear - M1 M2; lia. }
assert (Hbufc : (re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
   Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
   garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))))
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Hpn : re_buf e1 = 0 \/ In (re_buf e1, re_cap e1) (ablocks B ly1 S1))
  by (destruct Hbufc as [(_ & Hq & _)|(_ & Hq & _)]; [left; exact Hq | right; exact Hq]).
destruct (dt_gx_open_xR (G_DR B RG) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 [] W1 m1 md1 k1 HJ) as (memS & HSTK & HAG & HJi).
assert (HmokN : mo_ok MT S1 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT)).
{ pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmo0 & _).
  apply ((dt_mo_ok_of MT MMAX RG MTL HGSB) cx S1 spent tl); [exact Hmo0 | exact Hbud | exact HmoN|].
  rewrite Htl, (dt_tr_cost_app MT RG), Hev_co. clear - Hco2. lia. }
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (AREALLOC_R W1 regs1 m1 DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) memS (dxmd cx) []
    ly1 S1 [] md1 k1 (re_buf e1) (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) (- DRAIN_FRAME)
    (w64 (BASE + A_dr_rret)) [] (Z.to_nat (tr_cost MT_rk tl2) + kr)%nat HJi).
  - exact Hpn.
  - exact R10.
  - exact R11.
  - clear - Hnb Hmax Hal2. lia.
  - clear - Hlv1. lia.
  - unfold cnt_ok.
    eapply (cnt_ok_pk_mono RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 2)%nat) (fun _ => 0%nat)
      (ablocks B ly1 S1) (ablocks B ly1 S1)); [intros P; cbv beta; lia | exact HCNT1].
  - rewrite Hsp. unfold dsp0, DRAIN_FRAME. clear. lia.
  - reflexivity.
  - unfold DRAIN_FRAME. clear. lia.
  - assert (Hq : ASTACK - - DRAIN_FRAME <= DRAIN_STK_x) by (vm_compute; discriminate). exact Hq.
  - eapply aj_stack_room_xR with (o := - DRAIN_FRAME);
      [exact HJi | rewrite Hsp; clear; lia | vm_compute; discriminate].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact Hra.
  - unfold w64. apply ret_ok_codeptr_v; [unfold A_dr_rret, AF_fr_drain; lia
    | unfold A_dr_rret, AF_fr_drain; reflexivity].
  - apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) (rg_s RG) [] regs1).
    + apply achain_low. clear - HGS1 HGS2 C1. lia.
    + clear - HspA HspB Hsp. unfold DRAIN_FRAME in *. lia.
    + unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. clear - HGS1 HGS2. lia.
    + unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small
        by (unfold A_dr_rret, AF_fr_drain; clear - HBASE HBLO; lia). unfold A_dr_rret, AF_fr_drain. clear - HBASE HBLO; lia.
  - exact (RO_ARx _ _ _ _ _ _ (proj1 HJi)).
  - apply HA_call. exact HmokN.
  - unfold raZ. cbn [spine map]. rewrite Hra. unfold w64. rewrite unsigned_lit_small
      by (unfold A_dr_rret, AF_fr_drain; clear - HBASE HBLO; lia).
    replace (BASE + A_dr_rret) with (BASE + AF_fr_drain + 0x19c) by (unfold A_dr_rret; ring). exact HCTX_re1.
  - exact HRMc.
  - intros Hp0 Hin0 i Hi.
    assert (Hcap0 : 0 < re_cap e1)
      by (clear - Hbufc Hp0; destruct Hbufc as [(_ & Hq & _)|(Hq & _)]; [contradiction | lia]).
    assert (Hinbl : In (re_buf e1, re_cap e1) (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1)).
    { apply in_or_app. left. unfold aentry_blks.
      assert (Ec : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; clear - Hcap0; lia). rewrite Ec. left. reflexivity. }
    pose proof HBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
    apply (dt_buf_fp_x cx ly1 S1 [] W1 m1 md1 (aentry_blks e1 ++ asrc_blks h1 ++
      aout_blks (drain_b_c.ds_ocap s1) out1) (re_buf e1) (re_cap e1) HAR);
      [ (try rewrite <- !app_assoc); exact Hperm | exact Hinbl
      | (try rewrite <- !app_assoc); exact Hperm0 | exact Hin0 | clear - Hcapb; lia
      | clear - Hcap0 Hcapv; unfold ATABLE; lia | exact Hi ].
  - exact HmokN. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ2 & Hpres' & Hres10 & Hfrs2 &
  Hres4096 & HpermA & HpermB & Hcopy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
subst c2.
exact (dt_grow_post_xR cx kr s1 D W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl memS
  W2 ly2 S2 Hp2 regs2 mem2 md2 res tl2 HB Hregs Hra R10 R11 R19
  HMEM HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud0 Hroom Hncap Hnb Htl Hlater2
  HSTK HAG HJ2 Hpres' Hres10 Hfrs2 Hres4096 HpermA HpermB Hcopy Hkept2 Hmle2 HRM2 Herr2 Hpres2 K).
Qed.

Theorem dt_grow_xR : dt_grow_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr s1 D W1 c1 HB HDI Hlt K.
dt_hp0_x HB Hp.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDI as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hlater & Hbud).
dt_hp1_xR HMEM Hp1.
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 &
  F152 & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Hsaved).
pose proof HB as (Hafn & HSAreg & Htbl & HGle & HSAhi & HSA8 & HBrest).
pose proof Hafn as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR0 ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & Hq & _); exact Hq).
assert (Hcapb : 0 <= re_cap e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & Hq & _); destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Hucap : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
assert (Husedb : 0 <= re_used e1 <= 16384)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hl & _); lia).
assert (Hbufb : 0 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= alloc_ceiling).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _).
  destruct Hq as [(Hc & Hb & Hu)|(Hc & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hin) as (_ & H4 & Hcl & _).
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq). lia. }
pose proof HLINK as (Lcap & Lu & Lrest).
assert (Hulen : ulen s1 = re_used e1) by (unfold ulen; rewrite <- Lu, dt_bzs_len;
  pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hq & _); exact Hq).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (dt_gr_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 ltac:(lia)); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(lia) ltac:(lia)); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(lia) ltac:(lia)); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(lia) ltac:(lia)); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(lia) ltac:(lia)); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 0 E8 ltac:(lia) ltac:(lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite ((dt_den_gv RG) E (rg_s RG) 4 E8 ltac:(lia) ltac:(lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by lia; exact R26).
assert (HS : st_ok_pi SEGS VAL E ss_gr
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_top)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_gr. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dt_gr_frame, dt_gr_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold DRAIN_FRAME; lia|]. split; [unfold DRAIN_FRAME; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 32 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 32) / 8 <= dxSA cx + 32) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 16 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 16) / 8 <= dxSA cx + 16) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F224 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact ((dt_den_sh RG) E 32 (dxSA cx) 24 E32 E35 ltac:(lia) ltac:(lia))
          | unfold shadow_addr, SHADOW_OFF;
            (split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]
                    | assert (Hq : (dxSA cx + 24) / 8 <= dxSA cx + 24) by (apply Z.div_le_upper_bound; lia);
                      zside])
          | zside | exact F232 ].
    + cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 36 0) (re_buf e1));
          [exact (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_buf RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [exact (den_atom0 E 34 (re_used e1) E34 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_used RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [exact (den_atom0 E 33 (re_cap e1) E33 ltac:(lia)) | zside | zside | ].
        exact ((dt_entry_cap RG HGSB) W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr).
  - apply pairwise_disjoint_of_extents. unfold dt_gr_frame, dt_gr_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [dt_gr_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom E 32 (dxSA cx) E32 ltac:(lia)).
  - lia.
  - lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. lia. }
paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUNG BRR HS SHOK DBspan.
- rewrite ((dt_bnez_room RG HGSB) E (re_cap e1) (re_used e1) U33 U34 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.leb_le in Hc. rewrite <- Lcap, Hulen in Hlt. lia.
- paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
  psrr_branch_tok RUNG BRR HS SHOK DBspan.
  all: rewrite ((dt_bnez_atom RG) E 33 (re_cap e1) E33 ltac:(lia)) in Hc0.
  + apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = re_cap e1 * 2).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap. apply Z.eqb_neq in Hc0. rewrite Hc0. reflexivity. }
    dt_reg_x HS (1%bv : bv 5) X1. dt_reg_x HS (2%bv : bv 5) X2. dt_reg_x HS (3%bv : bv 5) X3.
    dt_reg_x HS (4%bv : bv 5) X4. dt_reg_x HS (8%bv : bv 5) X8. dt_reg_x HS (9%bv : bv 5) X9.
    dt_reg_x HS (10%bv : bv 5) X10. dt_reg_x HS (11%bv : bv 5) X11. dt_reg_x HS (18%bv : bv 5) X18.
    dt_reg_x HS (19%bv : bv 5) X19. dt_reg_x HS (20%bv : bv 5) X20. dt_reg_x HS (21%bv : bv 5) X21.
    dt_reg_x HS (22%bv : bv 5) X22. dt_reg_x HS (24%bv : bv 5) X24. dt_reg_x HS (26%bv : bv 5) X26.
    dt_reg_x HS (27%bv : bv 5) X27.
    pmkst HS.
    refine (dt_grow_after_xR cx kr s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
      _ _ _ _ _ (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K).
    * unfold dregs_top.
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
      split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
      split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
      split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
      split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
      split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
      split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
      split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
      split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
             |rewrite X26; exact (eq_trans (eq_sym R26') R26)].
    * rewrite X1. change 240%nat with A_TEXT. rewrite (codeptr_val E 4304 HEI).
      unfold w64, A_dr_rret, AF_fr_drain. f_equal; lia.
    * rewrite X10, (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)). reflexivity.
    * rewrite X11, ((dt_den_sll RG HGSB) E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc. reflexivity.
    * rewrite X19, ((dt_den_sll RG HGSB) E 33 (re_cap e1) E33 ltac:(lia) ltac:(lia)), Hnc. reflexivity.
  + apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (dt_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    assert (Hnc : drain_b_c.ds_cap (dgrow s1) = 8192).
    { change (drain_b_c.ds_cap (dgrow s1)) with (gcap (drain_b_c.ds_cap s1) (ulen s1)).
      rewrite (dt_gcap_grow (drain_b_c.ds_cap s1) (ulen s1) ltac:(rewrite <- Lcap, Hulen; lia) Hlt).
      rewrite <- Lcap, Hc0. reflexivity. }
    dt_reg_x HS (1%bv : bv 5) X1. dt_reg_x HS (2%bv : bv 5) X2. dt_reg_x HS (3%bv : bv 5) X3.
    dt_reg_x HS (4%bv : bv 5) X4. dt_reg_x HS (8%bv : bv 5) X8. dt_reg_x HS (9%bv : bv 5) X9.
    dt_reg_x HS (10%bv : bv 5) X10. dt_reg_x HS (11%bv : bv 5) X11. dt_reg_x HS (18%bv : bv 5) X18.
    dt_reg_x HS (19%bv : bv 5) X19. dt_reg_x HS (20%bv : bv 5) X20. dt_reg_x HS (21%bv : bv 5) X21.
    dt_reg_x HS (22%bv : bv 5) X22. dt_reg_x HS (24%bv : bv 5) X24. dt_reg_x HS (26%bv : bv 5) X26.
    dt_reg_x HS (27%bv : bv 5) X27.
    pmkst HS.
    refine (dt_grow_after_xR cx kr s1 D W1 _ ly1 S1 (ms_mem ms1) _ k1 e1 h1 out1 ev1 LB1 spent jb aa tl HB
      _ _ _ _ _ (dt_DMEM_kept_xR cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 s1 out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)
      HnoNUL Hused HLINK HSAME HHIST HJ1 Hlt Hlater Hbud K).
    * unfold dregs_top.
      split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
      split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
      split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
      split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
      split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
      split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
      split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
      split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
      split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
      split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
      split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
             |rewrite X26; exact (eq_trans (eq_sym R26') R26)].
    * rewrite X1. change 240%nat with A_TEXT. rewrite (codeptr_val E 4304 HEI).
      unfold w64, A_dr_rret, AF_fr_drain. f_equal; lia.
    * rewrite X10, (den_atom0 E 36 (re_buf e1) E36 ltac:(lia)). reflexivity.
    * rewrite X11, Hnc. cbn [sv_denot]. reflexivity.
    * rewrite X19, Hnc. cbn [sv_denot]. reflexivity.
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_trans for R_trans; the
   statements are the strict ones, checked by conversion).  At wle realloc #1's R rule is the strict AREALLOC
   (arealloc_cf_rule_c_xR_of_x), with RO and HA at True. ---- *)
Lemma dt_DMEM_kept_x : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
AJ0 cx ly1 S1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM0 cx ly1 S1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof. exact (dt_DMEM_kept_xR (@wle SEGS)). Qed.

Lemma dt_gx_open_x : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof. exact (dt_gx_open_xR (@wle SEGS)). Qed.
Lemma dt_gx_close_x : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof. exact (dt_gx_close_xR (@wle SEGS)). Qed.

Theorem dt_nogrow_x : dt_nogrow_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dt_nogrow_xR (@wle SEGS)). Qed.

Lemma dt_grow_core_x : forall cx kr s1 (W1 : world SEGS) ly1 S1 m1 md1 k1 e1 h1 out1 ev1 sent LB1
  (W2 : world SEGS) ly2 S2 mem2 md2 m3 md3 res nc,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1 ->
DLINK s1 e1 h1 -> re_used e1 <= APARTIAL ->
drain_b_c.ds_cap (dgrow s1) = nc ->
nc = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) -> 8192 <= nc <= 16384 ->
AR0 ly2 S2 W2 mem2 md2 -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2) ((res, nc) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, nc) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) nc ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size nc) \/ (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
AJ0 cx ly2 S2 W2 m3 md3 (k1 + 3) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 16 <= x < dxSA cx + 24) -> ~ (dxSA cx + 32 <= x < dxSA cx + 40) ->
   aview SEGS (w_H W2) m3 x = aview SEGS (w_H W2) mem2 x) ->
(forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m3 x) ->
val_mem SEGS (arm W2 m3) (dxSA cx + 16) 8 res ->
val_mem SEGS (arm W2 m3) (dxSA cx + 32) 8 nc ->
exists junk,
  DMEM0 cx ly2 S2 W2 m3 md3 (k1 + 3) (dt_ge e1 res nc junk) h1 (dgrow s1) out1 ev1 sent LB1 /\
  DLINK (dgrow s1) (dt_ge e1 res nc junk) h1.
Proof. exact (dt_grow_core_xR (@wle SEGS)). Qed.

Lemma dt_grow_post_x : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl
  memS (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 res tl2,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
4096 <= drain_b_c.ds_cap (dgrow s1) - ulen (dgrow s1) ->
drain_b_c.ds_cap (dgrow s1) = (if re_cap e1 =? 0 then 8192 else re_cap e1 * 2) ->
8192 <= drain_b_c.ds_cap (dgrow s1) <= 16384 ->
tl = fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa)) ++ tl2 ->
dlater cx (dgrow s1)
  (jb + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s1) (ulen s1) jb (drain_b_c.da_buf aa))))
  (agrow s1 jb aa) tl2 ->
0 <= DRAIN_STK_x -> gagree (G_DR B RG) (w_H (dxW cx)) (dxmem cx) memS ->
ajournal_x SEGS B PST ARx DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) [] (dxW cx) memS (dxmd cx) []
  ly2 S2 Hp2 W2 mem2 md2 (k1 + 3) ->
aregs_preserved regs1 regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S1 -> 4096 <= res ->
(re_buf e1 = 0 -> Permutation (ablocks B ly2 S2)
   ((res, drain_b_c.ds_cap (dgrow s1)) :: ablocks B ly1 S1)) ->
(re_buf e1 <> 0 -> exists l1 l2, ablocks B ly1 S1 = l1 ++ (re_buf e1, re_cap e1) :: l2 /\
   Permutation (ablocks B ly2 S2) ((res, drain_b_c.ds_cap (dgrow s1)) :: l1 ++ l2)) ->
(re_buf e1 <> 0 -> forall i, 0 <= i < Z.min (re_cap e1) (drain_b_c.ds_cap (dgrow s1)) ->
   aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) m1 (re_buf e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 m1 W2 mem2 (dsp0 cx - DRAIN_FRAME - ASTACK) (dsp0 cx - DRAIN_FRAME)
  (fun a => (res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
            (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
mo_le MT S1 S2 (mo_malloc MT (drain_b_c.ds_cap (dgrow s1)) + mo_free MT) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tl2) + kr) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) ->
   ~ ((res <= a < res + req_size (drain_b_c.ds_cap (dgrow s1))) \/
      (re_buf e1 <> 0 /\ re_buf e1 <= a < re_buf e1 + req_size (re_cap e1))) ->
   apresent (w_H W1) m1 a -> apresent (w_H W2) mem2 a) ->
(forall W3 c3, DT1x cx [] kr (dgrow s1) D W3 c3 -> SRr SEGS W3 c3 (dPOST_x B PST ARx MT RP RG cx [] kr)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + A_dr_rret)) mem2 (seg_rom SEGS)) md2) (dPOST_x B PST ARx MT RP RG cx [] kr).
Proof. exact (dt_grow_post_xR (@wle SEGS)). Qed.

Lemma dt_grow_after_x : forall cx kr s1 D (W1 : world SEGS) regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa tl,
DBASE_x B ARx MT RP MMAX RG cx [] kr ->
dregs_top RG cx regs1 ->
getr regs1 1 = w64 (BASE + A_dr_rret) ->
getr regs1 10 = w64 (re_buf e1) -> getr regs1 11 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
getr regs1 19 = w64 (drain_b_c.ds_cap (dgrow s1)) ->
DMEM0 cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
~ In (Z_to_bv 8 0) (re_U e1) -> re_used e1 <= APARTIAL ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 ->
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_cap s1 - ulen s1 < 4096 ->
dlater cx s1 jb aa tl -> dbud0 cx kr ly1 S1 spent tl ->
(forall W2 c2, DT1x cx [] kr (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx [] kr)) ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (SIGMA WS_realloc)) m1 (seg_rom SEGS)) md1) (dPOST_x B PST ARx MT RP RG cx [] kr).
Proof.
exact (dt_grow_after_xR (@wle SEGS) (@wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ => True)
  (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ _ => I) ltac:(apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC)).
Qed.

Theorem dt_grow_x : dt_grow_stmt_x B PST ARx MT RP MMAX RG.
Proof.
exact (dt_grow_xR (@wle SEGS) (@wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ => True)
  (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ _ => I) ltac:(apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC)).
Qed.

End cxh.
End b.
End a.

(* the zify flag a file that Requires this one saw before the generic kit was Required here (false: W_drain_topb_cx.v's
   setting), so that the kit's Requires above change nothing downstream *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
