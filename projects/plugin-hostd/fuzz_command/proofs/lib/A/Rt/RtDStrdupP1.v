(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2s.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build and its Zify flag line made Local. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE2s.v; 594 of its 635 lines of code are new or changed and 668 lines of the source are left out. *)
(* The first stretch of plugin-hostd/fuzz_command's strdup entry: from the trampoline 0x451dc through the prologue
   of ___interceptor_strdup 0x4ccb0, internal_strlen 0x69b10, the overflow test 0x4cd20 and the 64-byte split
   0x4cd28, to the join 0x4cd64 of the two range checks (the inline shadow check 0x4cd38 for a length under 64,
   __asan_region_is_poisoned 0x5a1ac for 64 and over). The run is symbolic over tbl_sd with a stack region of
   2,304 bytes below the entry sp; internal_strlen (RtSIstrlen.tfib_istrlen) is crossed with sd_call, the inline
   check (RtDStrdupS.sds_block) as plain msteps, and the range check through its contract. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI RtSRegionDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDStrdupD RtDStrdupF RtDStrdupH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtDStrdupS RtSIstrlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section p1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the statement ---- *)
Definition sd_saved (W : world tfibsegs) (mem : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 72) 8 (bv_unsigned (getr regs 23)).

Definition sd_p1_post (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (x len : Z) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs 0x4cd64 regs1 mem1 md1 /\
AR tfibsegs B ly S W mem1 md1 /\ same_but_materialized md md1 /\
getr regs1 2 = w64 (spZ regs - 2144) /\
getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 (spZ regs) /\ getr regs1 9 = w64 x /\ getr regs1 18 = w64 (len + 1) /\
getr regs1 22 = w64 (spZ regs - 2144) /\ getr regs1 23 = w64 (spZ regs - 2128) /\
(forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr regs1 r = getr regs r) /\
sd_saved W mem1 (spZ regs) regs /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2304 <= a < spZ regs) ->
 aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a).

(* ---- the symbolic states, measured on the pinned image ---- *)
Definition p1_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-2304) 0 (-2304) 0 [].
Definition p1_facts : list (nat * afact) := [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47) 0)].
Definition p1_ss0 : sstate := mkSS SD_TRAMP sr_atoms (p1_stk :: map ro_region sd_rodata) None (mkFacts p1_facts [] []).
Definition p1_RUN (s : sstate) := sym_runN tfibsegs tbl_sd FUEL s.
Definition p1_RUNTO (pc : Z) (s : sstate) := sym_run_toN tfibsegs tbl_sd FUEL pc s.
Definition p1_add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
(* the trampoline and the prologue, up to the call of internal_strlen *)
Definition p1_eA : sstate := Eval vm_compute in fst (p1_RUNTO 0x69b10 p1_ss0).
Lemma p1_rA : p1_RUNTO 0x69b10 p1_ss0 = (p1_eA, RS_running). Proof. vm_compute. reflexivity. Qed.
(* after internal_strlen: a0 is the atom 44, the length *)
Definition p1_pB : sstate := p1_add_fact (ss_after_call p1_eA (ss_mem p1_eA) 40 0x4cd00) 44 (mkAF 0 (2 ^ 32 - 2) 0).
Definition p1_eC : sstate := Eval vm_compute in fst (p1_RUN p1_pB).
Lemma p1_rC : p1_RUN p1_pB = (p1_eC, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 44 1))).
Proof. vm_compute. reflexivity. Qed.
(* the overflow test 0x4cd20 not taken *)
Definition p1_pD : sstate := add_cond p1_eC (mkAC (neg_bc BC_LTU) (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 44 1)).
Definition p1_eD : sstate := Eval vm_compute in fst (p1_RUN p1_pD).
Lemma p1_rD : p1_RUN p1_pD = (p1_eD, RS_stopped (SR_branch BC_GEU (SOff 44 0) (SLit 64))).
Proof. vm_compute. reflexivity. Qed.
(* the 64-byte split 0x4cd28: the big arm runs to the call of the range check, the small one to the inline check *)
Definition p1_pBig : sstate := add_cond p1_eD (mkAC BC_GEU (SOff 44 0) (SLit 64)).
Definition p1_eBig : sstate := Eval vm_compute in fst (p1_RUNTO 0x5a1ac p1_pBig).
Lemma p1_rBig : p1_RUNTO 0x5a1ac p1_pBig = (p1_eBig, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition p1_pSm : sstate := add_cond p1_eD (mkAC (neg_bc BC_GEU) (SOff 44 0) (SLit 64)).
Definition p1_eSm : sstate := Eval vm_compute in fst (p1_RUNTO 0x4cd38 p1_pSm).
Lemma p1_rSm : p1_RUNTO 0x4cd38 p1_pSm = (p1_eSm, RS_running). Proof. vm_compute. reflexivity. Qed.

(* ---- reading the states ---- *)
Definition p1_reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) v.
Definition p1_KEEP : list Z := [3; 4; 24; 25; 26; 27].
Definition p1_shapeJ (ss : sstate) : bool :=
p1_reg_is ss 2 (SOff 2 (-2144)) && p1_reg_is ss 8 (SOff 2 0) && p1_reg_is ss 9 (SOff 10 0) &&
p1_reg_is ss 18 (SOff 44 1) && p1_reg_is ss 22 (SOff 2 (-2144)) && p1_reg_is ss 23 (SOff 2 (-2128)) &&
forallb (fun r => p1_reg_is ss r (SOff (Z.to_nat r) 0)) p1_KEEP.
Definition p1_chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition p1_stk_head (ss : sstate) : bool :=
match ss_mem ss with
| r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? -2304) && (YP09.r_whi r =? 0)
| [] => false end.
Definition p1_has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (p1_chunk_is off v) (YP09.r_chunks r) | [] => false end.
(* ra, s0, s1 .. s7 at these offsets below the entry sp *)
Definition p1_SAVED : list (Z * Z) :=
[(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72)].
Definition p1_shapeS (ss : sstate) : bool :=
p1_stk_head ss && forallb (fun p => p1_has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) p1_SAVED.
Definition p1_win_ok (rs : smem) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, -2304, 0) || (snd t <=? snd (fst t))) (windows rs).

Definition p1_regs_ok (regs regs1 : bvmap 5 word) (x len : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 2144) /\
getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 (spZ regs) /\ getr regs1 9 = w64 x /\ getr regs1 18 = w64 (len + 1) /\
getr regs1 22 = w64 (spZ regs - 2144) /\ getr regs1 23 = w64 (spZ regs - 2128) /\
(forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr regs1 r = getr regs r).

Lemma p1_RD : forall H E ss ms (r : bv 5) v, st_ok tfibsegs E ss (restrict H ms) ->
p1_reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v.
Proof.
intros H E ss ms r v HS Hr. unfold p1_reg_is in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
rewrite <- Hr. exact (st_ok_reg_denot H E ss ms r HS).
Qed.

Lemma p1_regs_of_shape : forall H E ss ms (regs : bvmap 5 word) x len,
st_ok tfibsegs E ss (restrict H ms) ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
ew E 44 = w64 len -> 0 <= len < 2 ^ 32 -> getr regs 10 = w64 x -> 0 <= x < 2 ^ 64 ->
p1_shapeJ ss = true -> p1_regs_ok regs (ms_regs ms) x len.
Proof.
intros H E ss ms regs x len HS Hreg H44 Hlen G10 Hx Hsh. unfold p1_shapeJ in Hsh.
apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R23]. apply andb_prop in Hsh as [Hsh R22].
apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [R2 R8].
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Hreg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (apply Hreg; reflexivity).
assert (KA : forall r : bv 5, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 24 <= bv_unsigned r <= 27) ->
getr (ms_regs ms) r = getr regs r).
{ intros r Hr. pose proof (u5_range r) as Hr5.
  assert (Hin : In (bv_unsigned r) p1_KEEP) by (unfold p1_KEEP; cbn [In]; lia).
  rewrite forallb_forall in HK. specialize (HK _ Hin). cbv beta in HK.
  rewrite (p1_RD H E ss ms r _ HS HK). cbn [sv_denot].
  rewrite (Hreg (Z.to_nat (bv_unsigned r)) r) by (rewrite Z2Nat.id; lia).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
unfold p1_regs_ok.
split; [rewrite (p1_RD H E ss ms 2%bv (SOff 2 (-2144)) HS R2); cbn [sv_denot]; rewrite E2; reflexivity|].
split; [apply KA; left; reflexivity|].
split; [apply KA; right; left; reflexivity|].
split; [rewrite (p1_RD H E ss ms 8%bv (SOff 2 0) HS R8); cbn [sv_denot]; rewrite E2, Z.add_0_r; reflexivity|].
split.
{ rewrite (p1_RD H E ss ms 9%bv (SOff 10 0) HS R9). cbn [sv_denot]. rewrite E10, G10, Z.add_0_r.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
split.
{ rewrite (p1_RD H E ss ms 18%bv (SOff 44 1) HS R18). cbn [sv_denot]. rewrite H44.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
split; [rewrite (p1_RD H E ss ms 22%bv (SOff 2 (-2144)) HS R22); cbn [sv_denot]; rewrite E2; reflexivity|].
split; [rewrite (p1_RD H E ss ms 23%bv (SOff 2 (-2128)) HS R23); cbn [sv_denot]; rewrite E2; reflexivity|].
intros r Hr. apply KA. right. right. exact Hr.
Qed.

Lemma p1_chunk_sound : forall off v c, p1_chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold p1_chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.

Lemma p1_saved_of_shape : forall (W : world tfibsegs) E ss ms (regs : bvmap 5 word),
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
p1_shapeS ss = true -> sd_saved W (ms_mem ms) (spZ regs) regs.
Proof.
intros W E ss ms regs HS Hreg Hsh. unfold p1_shapeS in Hsh. apply andb_prop in Hsh as [Hhd HSV].
unfold p1_stk_head in Hhd.
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Hhd as [Hhd _]. apply andb_prop in Hhd as [Hbase _]. apply obase_eqb_eq in Hbase.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Hreg 2%nat 2%bv eq_refl); reflexivity).
assert (CK : forall j rz off, nth_error p1_SAVED j = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
  assert (Hrz : 0 <= rz < 32) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
  unfold p1_has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply p1_chunk_sound in Hc. subst c.
  pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
  pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E2 in Hck.
  apply (val_of_chunk_ok tfibsegs E _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
  - cbn [sv_denot]. rewrite (Hreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
  - pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
  - zside. }
unfold sd_saved.
split; [replace (spZ regs - 8) with (spZ regs + -8) by lia; exact (CK 0%nat 1 (-8) eq_refl)|].
split; [replace (spZ regs - 16) with (spZ regs + -16) by lia; exact (CK 1%nat 8 (-16) eq_refl)|].
split; [replace (spZ regs - 24) with (spZ regs + -24) by lia; exact (CK 2%nat 9 (-24) eq_refl)|].
split; [replace (spZ regs - 32) with (spZ regs + -32) by lia; exact (CK 3%nat 18 (-32) eq_refl)|].
split; [replace (spZ regs - 40) with (spZ regs + -40) by lia; exact (CK 4%nat 19 (-40) eq_refl)|].
split; [replace (spZ regs - 48) with (spZ regs + -48) by lia; exact (CK 5%nat 20 (-48) eq_refl)|].
split; [replace (spZ regs - 56) with (spZ regs + -56) by lia; exact (CK 6%nat 21 (-56) eq_refl)|].
split; [replace (spZ regs - 64) with (spZ regs + -64) by lia; exact (CK 7%nat 22 (-64) eq_refl)|].
replace (spZ regs - 72) with (spZ regs + -72) by lia. exact (CK 8%nat 23 (-72) eq_refl).
Qed.

Lemma p1_saved_move : forall (W : world tfibsegs) m m' sp0 regs,
sd_saved W m sp0 regs ->
(forall a, sp0 - 72 <= a < sp0 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
sd_saved W m' sp0 regs.
Proof.
intros W m m' sp0 regs (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9) K.
unfold sd_saved.
repeat split; eapply AE2y.val_mem_kept; try eassumption; intros k Hk; apply K; change (Z.of_nat 8) with 8 in Hk; lia.
Qed.

(* ---- the memory outside the stack window ---- *)
Lemma p1_meq : forall E rs (m m' : word -> option byte) sp0,
p1_win_ok rs = true -> bv_unsigned (ew E 2) = sp0 -> frame_of E rs m m' ->
forall z : word, ~ (sp0 - 2304 <= bv_unsigned z < sp0) -> m' z = m z.
Proof.
intros E rs m m' sp0 Hw E2 HF z Hz. apply HF. intros Hin.
pose proof (in_wrange_single_b E rs (bv_unsigned z) 2 (-2304) 0 sp0 Hw E2 Hin) as X. lia.
Qed.

Lemma p1_av : forall (H : word -> bool) (mem mem' : word -> option byte) sp0,
(forall z : word, ~ (sp0 - 2304 <= bv_unsigned z < sp0) -> mem' z = mem z) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2304 <= a < sp0) -> aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' sp0 MEQ a Hr Ha. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Ha. Qed.

Lemma p1_win_present : forall H E ss ms sp0,
st_ok tfibsegs E ss (restrict H ms) -> p1_stk_head ss = true -> bv_unsigned (ew E 2) = sp0 ->
2 ^ 44 <= sp0 -> sp0 <= 2 ^ 64 ->
forall a, sp0 - 2304 <= a < sp0 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms sp0 HS Hhd E2 Hlo Hhi a Ha. unfold p1_stk_head in Hhd.
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Hhd as [Hhd Hwhi]. apply andb_prop in Hhd as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi.
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. lia.
Qed.

Lemma p1_pres_move : forall (H : word -> bool) (mem mem' : word -> option byte) sp0,
(forall z : word, ~ (sp0 - 2304 <= bv_unsigned z < sp0) -> mem' z = mem z) ->
(forall a, sp0 - 2304 <= a < sp0 -> apresent H mem' a) ->
forall a, apresent H mem a -> apresent H mem' a.
Proof.
intros H mem mem' sp0 MEQ PR a Hp. rewrite (AE2y.apresent_mod _ mem' a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2304)) as [L1|L1].
{ apply (apresent_same H mem mem' a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
destruct (Z_lt_le_dec a' sp0) as [L2|L2]; [apply PR; lia|].
apply (apresent_same H mem mem' a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp].
Qed.

(* AR survives a change of the memory inside the stack window and of the materialized part of the model *)
Lemma p1_AR_move : forall B, AR_laws tfibsegs B -> forall ly S (W : world tfibsegs) mem md mem' md' sp0,
AR tfibsegs B ly S W mem md -> 0 <= sp0 - 2304 -> ly_stk_lo ly <= sp0 - 2304 -> sp0 <= ly_stk_hi ly -> sp0 <= 2 ^ 64 ->
(forall z : word, ~ (sp0 - 2304 <= bv_unsigned z < sp0) -> mem' z = mem z) ->
(forall a, sp0 - 2304 <= a < sp0 -> apresent (w_H W) mem a) ->
(forall a, sp0 - 2304 <= a < sp0 -> apresent (w_H W) mem' a) ->
same_but_materialized md md' -> AR tfibsegs B ly S W mem' md'.
Proof.
intros B LAWS ly S W mem md mem' md' sp0 HAR H0 Hlo Hhi Hsp MEQ P0 P1 SBM.
destruct (same_but_materialized_frame md md' SBM) as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
apply (al_frame _ _ LAWS ly S W mem md mem' md' HAR).
- intros a Hr Hown. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. intros Hs.
  exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
- intros a Hv. rewrite (AE2y.aview_mod _ mem' a). rewrite (AE2y.aview_mod _ mem a) in Hv.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (sp0 - 2304)) as [L1|L1].
  { rewrite (aview_same _ mem mem'); [exact Hv | apply MEQ; rewrite unsigned_lit_small by lia; lia]. }
  destruct (Z_lt_le_dec a' sp0) as [L2|L2]; [apply AE2y.aview_some_of_apresent; apply P1; lia|].
  rewrite (aview_same _ mem mem'); [exact Hv | apply MEQ; rewrite unsigned_lit_small by lia; lia].
- exact V1.
- exact V2.
- exact V3.
- exact (AE2y.hs_kept_win (w_H W) mem mem mem' (sp0 - 2304) sp0 (sp0 - 2304) sp0 MEQ P0 (Z.le_refl _) (Z.le_refl _)).
Qed.

Lemma p1_AR_md : forall B, AR_laws tfibsegs B -> forall ly S (W : world tfibsegs) mem md md',
AR tfibsegs B ly S W mem md -> same_but_materialized md md' -> AR tfibsegs B ly S W mem md'.
Proof.
intros B LAWS ly S W mem md md' HAR Hs.
destruct (same_but_materialized_frame md md' Hs) as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
exact (al_frame _ _ LAWS ly S W mem md mem md' HAR (fun _ _ _ => eq_refl) (fun _ H => H) V1 V2 V3 (fun _ _ _ => eq_refl)).
Qed.

(* the read premise of the entry, carried to a later memory and to the range check's 72-byte window *)
Lemma p1_aread_move : forall (W : world tfibsegs) regs regs' mem mem' x n,
aread_ok tfibsegs ASTACK W regs mem x n -> 0 < n ->
0x10007fff8000 + 16384 <= spZ regs -> spZ regs <= 2 ^ 47 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2304 <= a < spZ regs) ->
 aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
spZ regs - 2304 <= spZ regs' - 72 -> spZ regs' <= spZ regs ->
aread_ok tfibsegs 72 W regs' mem' x n.
Proof.
intros W regs regs' mem mem' x n (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hn Hlo Hhi AV Hs1 Hs2.
assert (Hxn : x + n <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H5; lia).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [|split; [exact H5|split]].
- intros a Ha. destruct (H4 a Ha) as [V N]. unfold ascratch_stk, ASTACK in N |- *. split; [|lia].
  rewrite AV by lia. exact V.
- eapply range_addressable_agree; [|exact H6]. intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
  pose proof (AE2y.shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
  apply AV; lia.
- intros _ s Hs. specialize (H7 Hn).
  pose proof (AE2y.shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2].
  pose proof (AE2y.shadow_addr_bounds (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2].
  unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2.
  pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)).
  pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)).
  rewrite AV by lia. exact (H7 s Hs).
Qed.

(* every read-only byte of the image lies below 0x148680 (RtSStrnlen.v snl_rom_low) *)
Lemma p1_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < 0x148680.
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. remember (seg_writable sg) as wr eqn:Ew. clear Eb Ez Ew.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-; try discriminate; lia.
Qed.

(* ---- registers ---- *)
Lemma p1_ne_bv5 : forall (z : Z) (k : bv 5), 0 <= z < 32 -> z <> bv_unsigned k -> Z_to_bv 5 z <> k.
Proof.
intros z k Hz Hne E. apply Hne. rewrite <- E. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma p1_keep_ap : forall r1 r2 : bvmap 5 word,
(forall r : bv 5, RtDStrdupS.keepS r -> getr r2 r = getr r1 r) -> aregs_preserved r1 r2.
Proof.
intros r1 r2 K z Hz. apply K. unfold RtDStrdupS.keepS. unfold acallee_saved in Hz.
repeat split; (apply p1_ne_bv5; [lia | vm_compute; lia]).
Qed.

Lemma p1_regs_ok_tr : forall regs r1 r2 x len, p1_regs_ok regs r1 x len -> aregs_preserved r1 r2 -> p1_regs_ok regs r2 x len.
Proof.
intros regs r1 r2 x len (A2 & A3 & A4 & A8 & A9 & A18 & A22 & A23 & A24) K.
assert (K' : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> getr r2 rr = getr r1 rr)
by (intros z rr -> Hz; exact (K z Hz)).
unfold p1_regs_ok.
split; [rewrite (K' 2 2%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A2|].
split; [rewrite (K' 3 3%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A3|].
split; [rewrite (K' 4 4%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A4|].
split; [rewrite (K' 8 8%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A8|].
split; [rewrite (K' 9 9%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A9|].
split; [rewrite (K' 18 18%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A18|].
split; [rewrite (K' 22 22%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A22|].
split; [rewrite (K' 23 23%bv ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)); exact A23|].
intros r Hr. rewrite (K' (bv_unsigned r) r (eq_sym (Z_to_bv_bv_unsigned 5 r)) ltac:(unfold acallee_saved; lia)).
exact (A24 r Hr).
Qed.

(* ---- branches ---- *)
(* 0x4cd20: bltu ~x, len + 1 is never taken *)
Lemma p1_br_ovf : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n ->
0 <= d <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 1)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn.
rewrite branch_ltu_U, AE2y.U_not, (U_atom E pa d Hd), (U_atom_off E pn n 1 Hn) by lia.
apply Z.ltb_ge. lia.
Qed.

(* 0x4cd28: bgeu len, 64 *)
Lemma p1_br_len64 : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 0 <= n < 2 ^ 32 ->
branch_taken BC_GEU (sv_denot E (SOff pn 0)) (sv_denot E (SLit 64)) = negb (n <? 64).
Proof. intros E pn n Hn Rn. rewrite branch_geu_U, (U_lit E 64), (U_atom E pn n Hn) by lia. reflexivity. Qed.

(* 0x4cf8c: beqz a0, 0x4cd64, taken when the range check answers 0 *)
Lemma p1_fetch_lit : forall (p : word) (w : bv 32),
clookup tbl_sd (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_sd_ok. exact H. Qed.
Lemma p1_F_f8c : fetch_word tfibsegs (Z_to_bv 64 0x4cf8c) = Some (0xdc050ce3%bv : bv 32).
Proof. apply p1_fetch_lit. vm_compute. reflexivity. Qed.
Lemma p1_D_f8c : decode_any (0xdc050ce3%bv : bv 32) = Some (Branch BC_EQ 10 0 7640, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma p1_mst_refl_pc : forall regs (pc pc' : word) mem rom, bv_unsigned pc = bv_unsigned pc' ->
msteps tfibsegs (mkst regs pc mem rom) (mkst regs pc' mem rom).
Proof. intros regs pc pc' mem rom E. replace pc' with pc by (apply bv_eq; exact E). apply mst_refl. Qed.
Lemma p1_beqz_step : forall regs m rom, getr regs 10 = Z_to_bv 64 0 ->
msteps tfibsegs (mkst regs (Z_to_bv 64 0x4cf8c) m rom) (mkst regs (Z_to_bv 64 0x4cd64) m rom).
Proof.
intros regs m rom H10.
eapply mst_step; [reflexivity | eapply step_branch_tk_gen; [exact p1_F_f8c | reflexivity | exact p1_D_f8c |] |].
- rewrite H10, getr_zero. vm_compute. reflexivity.
- apply p1_mst_refl_pc. vm_compute. reflexivity.
Qed.

(* ---- small helpers ---- *)
Lemma p1_st_ok_add_fact : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (p1_add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, p1_add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.

Lemma p1_SRr_msteps_mem : forall (W0 : world tfibsegs) regs0 pc0 mem0 md0 regs1 pc1 Q,
msteps tfibsegs (mkst regs0 pc0 (mrestrict (w_H W0) mem0) (seg_rom tfibsegs))
(mkst regs1 pc1 (mrestrict (w_H W0) mem0) (seg_rom tfibsegs)) ->
(forall md1, same_but_materialized md0 md1 -> SRr tfibsegs W0 (mkCfg (mkst regs1 pc1 mem0 (seg_rom tfibsegs)) md1) Q) ->
SRr tfibsegs W0 (mkCfg (mkst regs0 pc0 mem0 (seg_rom tfibsegs)) md0) Q.
Proof.
intros W0 regs0 pc0 mem0 md0 regs1 pc1 Q Hms HK.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W0); [rewrite restrict_mkst_fx; exact Hms|].
intros md1 Hs _. change (ms_mem (mkst regs0 pc0 mem0 (seg_rom tfibsegs))) with mem0.
rewrite unrestrict_mkst_mrestrict. exact (HK md1 Hs).
Qed.

(* ---- the small arm: 0x4cd38, the inline check, 0x4cd64 ---- *)
Lemma p1_arm_small : forall B, AR_laws tfibsegs B ->
forall ly S (W : world tfibsegs) regs mem md x len E ms mdk,
AR tfibsegs B ly S W mem md ->
ly_stk_lo ly + ASTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x -> 0 <= len < 64 ->
aread_ok tfibsegs ASTACK W regs mem x (len + 1) ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
ew E 44 = w64 len ->
st_ok tfibsegs E p1_pSm (restrict (w_H W) ms) ->
(forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms z = mem z) ->
same_but_materialized md mdk ->
SRr tfibsegs W (mkCfg ms mdk) (sd_p1_post B ly S W regs mem md x len).
Proof.
intros B LAWS ly S W regs mem md x len E ms mdk HAR Hslo Hshi Hpres G10 Hx Hlen HRD Ereg E44 HS MEQ SBM.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, Hpres.
pose proof HRD as (_ & _ & _ & _ & Ham & _ & _).
assert (Hamr : x + (len + 1) <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Ereg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 x) by (rewrite (Ereg 10%nat 10%bv eq_refl); exact G10).
eapply SRr_bind; [apply (sd_phase_to W E 0x4cd38 p1_pSm p1_eSm RS_running ms mdk HS p1_rSm)|].
cbv beta iota. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & _).
assert (MEQ5 : forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (p1_meq E (ss_mem p1_pSm) _ _ (spZ regs) ltac:(vm_compute; reflexivity) E2 HF5 z Hz). exact (MEQ z Hz). }
pose proof (p1_av (w_H W) mem (ms_mem ms5) (spZ regs) MEQ5) as AV5.
assert (PR5 : forall a, spZ regs - 2304 <= a < spZ regs -> apresent (w_H W) (ms_mem ms5) a).
{ intros a Ha. apply (p1_win_present (w_H W) E p1_eSm ms5 (spZ regs) HS5 ltac:(vm_compute; reflexivity) E2); lia. }
(* the registers the inline check reads *)
assert (R10 : getr (ms_regs ms5) 10 = Z_to_bv 64 len).
{ rewrite (p1_RD (w_H W) E p1_eSm ms5 10%bv (SOff 44 0) HS5 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E44. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (R11 : getr (ms_regs ms5) 11 = Z_to_bv 64 RtDStrdupS.SD_SB)
by (rewrite (p1_RD (w_H W) E p1_eSm ms5 11%bv (SLit 0x7fff8000) HS5 ltac:(vm_compute; reflexivity)); reflexivity).
assert (R9 : getr (ms_regs ms5) 9 = Z_to_bv 64 x).
{ rewrite (p1_RD (w_H W) E p1_eSm ms5 9%bv (SOff 10 0) HS5 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
(* the shadow premises over the memory at 0x4cd38 *)
pose proof (p1_aread_move W regs regs mem (ms_mem ms5) x (len + 1) HRD ltac:(lia) ltac:(lia) ltac:(lia) AV5 ltac:(lia) ltac:(lia))
as (_ & _ & _ & _ & _ & HRA5 & HHULL5).
specialize (HHULL5 ltac:(lia)).
(* the inline check 0x4cd38 -> 0x4cd64 *)
destruct (RtDStrdupS.sds_block x len (mrestrict (w_H W) (ms_mem ms5)) (seg_rom tfibsegs) Hx Hlen ltac:(lia)
(sd_granules W (ms_mem ms5) x len Hx Hlen HRA5)
(sd_last W (ms_mem ms5) x len Hlen HRA5)
(proj1 (sd_words W (ms_mem ms5) x len Hx Hlen ltac:(lia) HHULL5))
(proj2 (sd_words W (ms_mem ms5) x len Hx Hlen ltac:(lia) HHULL5))
(ms_regs ms5) R10 R11 R9) as (regs6 & pcf & Hms6 & Hpcf & K6).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E p1_eSm ms5 HS5 ltac:(vm_compute; reflexivity)) as Hshape.
rewrite Hshape.
apply (p1_SRr_msteps_mem W (ms_regs ms5) (Z_to_bv 64 (ss_pc p1_eSm)) (ms_mem ms5) _ regs6 pcf _ Hms6).
intros md6 SBM6.
assert (Hpc : pcf = Z_to_bv 64 0x4cd64) by (apply bv_eq; rewrite Hpcf; reflexivity).
subst pcf.
apply SRr_ret. unfold sd_p1_post. split; [reflexivity|].
exists regs6, (ms_mem ms5), md6. split; [reflexivity|].
assert (SBMf : same_but_materialized md md6).
{ eapply same_but_materialized_trans; [exact SBM|]. eapply same_but_materialized_trans; [apply with_vm_backing_same | exact SBM6]. }
split.
{ apply (p1_AR_move B LAWS ly S W mem md (ms_mem ms5) md6 (spZ regs) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MEQ5).
  - intros a Ha. apply Hpres. lia.
  - exact PR5.
  - exact SBMf. }
split; [exact SBMf|].
pose proof (p1_regs_of_shape (w_H W) E p1_eSm ms5 regs x len HS5 Ereg E44 ltac:(lia) G10 ltac:(lia) ltac:(vm_compute; reflexivity)) as RJ.
destruct (p1_regs_ok_tr regs (ms_regs ms5) regs6 x len RJ (p1_keep_ap _ _ K6)) as (A2 & A3 & A4 & A8 & A9 & A18 & A22 & A23 & A24).
split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A8|]. split; [exact A9|].
split; [exact A18|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|].
split; [exact (p1_saved_of_shape W E p1_eSm ms5 regs HS5 Ereg ltac:(vm_compute; reflexivity))|].
split; [exact AV5 | exact (p1_pres_move (w_H W) mem (ms_mem ms5) (spZ regs) MEQ5 PR5)].
Qed.

(* ---- the big arm: 0x4cf44, the range check 0x5a1ac, 0x4cf8c, 0x4cd64 ---- *)
Lemma p1_arm_big : forall B, AR_laws tfibsegs B -> aregion_zero_stk tfibsegs B PC_region_is_poisoned ->
forall ly S (W : world tfibsegs) regs mem md x len E ms mdk,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + ASTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x -> 64 <= len -> len + 1 < 2 ^ 32 ->
aread_ok tfibsegs ASTACK W regs mem x (len + 1) ->
rt_rom_view tfibsegs B W mem ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
ew E 44 = w64 len ->
st_ok tfibsegs E p1_pBig (restrict (w_H W) ms) ->
(forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms z = mem z) ->
same_but_materialized md mdk ->
SRr tfibsegs W (mkCfg ms mdk) (sd_p1_post B ly S W regs mem md x len).
Proof.
intros B LAWS RGN ly S W regs mem md x len E ms mdk HAR Hal16 Hslo Hshi Hpres G10 Hx Hlen64 Hn32 HRD HROM Ereg E44 HS MEQ SBM.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, Hpres.
pose proof HRD as (_ & _ & _ & _ & Ham & _ & _).
assert (Hamr : x + (len + 1) <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Ereg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 x) by (rewrite (Ereg 10%nat 10%bv eq_refl); exact G10).
eapply SRr_bind; [apply (sd_phase_to W E 0x5a1ac p1_pBig p1_eBig RS_running ms mdk HS p1_rBig)|].
cbv beta iota. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & _).
assert (MEQ5 : forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (p1_meq E (ss_mem p1_pBig) _ _ (spZ regs) ltac:(vm_compute; reflexivity) E2 HF5 z Hz). exact (MEQ z Hz). }
pose proof (p1_av (w_H W) mem (ms_mem ms5) (spZ regs) MEQ5) as AV5.
assert (PR5 : forall a, spZ regs - 2304 <= a < spZ regs -> apresent (w_H W) (ms_mem ms5) a).
{ intros a Ha. apply (p1_win_present (w_H W) E p1_eBig ms5 (spZ regs) HS5 ltac:(vm_compute; reflexivity) E2); lia. }
(* the registers at the call of the range check *)
assert (C1 : getr (ms_regs ms5) 1 = Z_to_bv 64 0x4cf8c)
by (rewrite (p1_RD (w_H W) E p1_eBig ms5 1%bv (SLit 0x4cf8c) HS5 ltac:(vm_compute; reflexivity)); reflexivity).
assert (C10 : getr (ms_regs ms5) 10 = w64 x).
{ rewrite (p1_RD (w_H W) E p1_eBig ms5 10%bv (SOff 10 0) HS5 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (C11 : getr (ms_regs ms5) 11 = w64 (len + 1)).
{ rewrite (p1_RD (w_H W) E p1_eBig ms5 11%bv (SOff 44 1) HS5 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite E44. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose proof (p1_regs_of_shape (w_H W) E p1_eBig ms5 regs x len HS5 Ereg E44 ltac:(lia) G10 ltac:(lia) ltac:(vm_compute; reflexivity)) as RJ.
pose proof (p1_saved_of_shape W E p1_eBig ms5 regs HS5 Ereg ltac:(vm_compute; reflexivity)) as SV.
assert (C2 : spZ (ms_regs ms5) = spZ regs - 2144).
{ unfold spZ at 1. rewrite (proj1 RJ). unfold w64. apply unsigned_lit_small. lia. }
assert (SBM5 : same_but_materialized md (with_vm_backing (m_vm_lazy mdk) mat5 mdk))
by (eapply same_but_materialized_trans; [exact SBM | apply with_vm_backing_same]).
assert (HAR5 : AR tfibsegs B ly S W (ms_mem ms5) (with_vm_backing (m_vm_lazy mdk) mat5 mdk)).
{ apply (p1_AR_move B LAWS ly S W mem md (ms_mem ms5) _ (spZ regs) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MEQ5).
  - intros a Ha. apply Hpres. lia.
  - exact PR5.
  - exact SBM5. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E p1_eBig ms5 HS5 ltac:(vm_compute; reflexivity)) as Hshape.
rewrite Hshape.
replace (Z_to_bv 64 (ss_pc p1_eBig)) with (w64 PC_region_is_poisoned) by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms5) (w64 PC_region_is_poisoned) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy mdk) mat5 mdk))
with (cfg_at tfibsegs PC_region_is_poisoned (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy mdk) mat5 mdk)).
(* the range check, through its contract at the 72-byte window *)
eapply SRr_bind.
{ apply (RGN RGN_SCR (Z.le_refl _) ly S W (ms_regs ms5) (ms_mem ms5) _ x (len + 1) HAR5).
  - rewrite C1. apply ret_ok_lit; [lia | reflexivity].
  - rewrite C2. replace (spZ regs - 2144) with (spZ regs + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite C2. unfold RGN_SCR. lia.
  - rewrite C2. lia.
  - intros a Ha. rewrite C2 in Ha. unfold RGN_SCR in Ha. apply PR5. lia.
  - exact C10.
  - exact C11.
  - lia.
  - exact Hx.
  - exact (p1_aread_move W regs (ms_regs ms5) mem (ms_mem ms5) x (len + 1) HRD ltac:(lia) ltac:(lia) ltac:(lia) AV5 ltac:(lia) ltac:(lia)).
  - apply (rt_rom_view_keep tfibsegs B W mem (ms_mem ms5) HROM). intros a Hrom _ _.
    pose proof (p1_rom_low a Hrom). apply AV5; lia. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HAR6 & AP6 & SBM6 & A10 & Hfr6 & Hpm6 & _).
assert (A10' : getr regs6 10 = Z_to_bv 64 0) by exact A10.
(* 0x4cf8c: beqz a0, 0x4cd64 *)
unfold cfg_at.
replace (w64 (raZ (ms_regs ms5))) with (Z_to_bv 64 0x4cf8c) by (unfold raZ, w64; rewrite C1, unsigned_lit_small by lia; reflexivity).
apply (p1_SRr_msteps_mem W regs6 (Z_to_bv 64 0x4cf8c) mem6 md6 regs6 (Z_to_bv 64 0x4cd64) _
(p1_beqz_step regs6 (mrestrict (w_H W) mem6) (seg_rom tfibsegs) A10')).
intros md7 SBM7. apply SRr_ret. unfold sd_p1_post. split; [reflexivity|].
exists regs6, mem6, md7. split; [reflexivity|].
split; [exact (p1_AR_md B LAWS ly S W mem6 md6 md7 HAR6 SBM7)|].
split; [eapply same_but_materialized_trans; [exact SBM5|]; eapply same_but_materialized_trans; [exact SBM6 | exact SBM7]|].
destruct (p1_regs_ok_tr regs (ms_regs ms5) regs6 x len RJ AP6) as (A2 & A3 & A4 & A8 & A9 & A18 & A22 & A23 & A24).
split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A8|]. split; [exact A9|].
split; [exact A18|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|].
split.
{ apply (p1_saved_move W (ms_mem ms5) mem6 (spZ regs) regs SV). intros a Ha.
  apply Hfr6; [lia | unfold ascratch_stk; rewrite C2; unfold RGN_SCR; lia | intros F; exact F]. }
split.
- intros a Hr Ha. rewrite Hfr6; [apply AV5; assumption | exact Hr | unfold ascratch_stk; rewrite C2; unfold RGN_SCR; lia | intros F; exact F].
- intros a Hp. apply Hpm6. exact (p1_pres_move (w_H W) mem (ms_mem ms5) (spZ regs) MEQ5 PR5 a Hp).
Qed.

(* ---- the stretch ---- *)
Theorem sd_p1_srr : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B ->
aregion_zero_stk tfibsegs B PC_region_is_poisoned ->
forall ly S (W : world tfibsegs) regs mem md (x len : Z) (s : list byte),
AR tfibsegs B ly S W mem md ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + ASTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 x -> 0 < x ->
astr_at tfibsegs W mem x s -> len = astr_len s ->
aread_ok tfibsegs ASTACK W regs mem x (len + 1) ->
len + 1 < 2 ^ 32 ->
rt_rom_view tfibsegs B W mem ->
SRr tfibsegs W (cfg_at tfibsegs PC_strdup regs mem md) (sd_p1_post B ly S W regs mem md x len).
Proof.
intros B LAWS TB RGN ly S W regs mem md x len s HAR Hret Hal16 Hslo Hshi Hpres Hgp Htp G10 Hx Hstr Hlen HRD Hn32 HROM.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= spZ regs <= 2 ^ 47) by (unfold ASTACK in Hslo; lia).
pose proof HRD as (Hx0 & Hxn & Hn & Hsrc & Ham & _ & _).
assert (Hamr : x + (len + 1) <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
destruct Hstr as (Hab & Hnul).
assert (Hls : len = Z.of_nat (length s)) by (rewrite Hlen; reflexivity).
unfold cfg_at. change (w64 PC_strdup) with (Z_to_bv 64 SD_TRAMP).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = spZ regs) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
(* the entry state *)
assert (HS0 : st_ok tfibsegs EE p1_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 SD_TRAMP) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold p1_ss0. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact (rodata_ok B TB sd_rodata ly S (w_H W) mem EE (sd_rodata_chk ly) (proj1 HAR))].
    unfold p1_stk. apply (region_ok_stack tfibsegs EE _ 2 (spZ regs) (-2304)); [exact EE2 | lia | lia |].
    intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END; lia|]. apply Hpres. unfold ASTACK; lia.
  - apply pairwise_disjoint_of_extents. unfold p1_stk, sd_rodata, icpt_rodata, ro_region, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok p1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2, EE10, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | lia]. }
(* the trampoline and the prologue, to the call of internal_strlen *)
eapply SRr_bind; [apply (sd_phase_to W EE 0x69b10 p1_ss0 p1_eA RS_running _ md HS0 p1_rA)|].
cbv beta iota. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
assert (MEQ1 : forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms1 z = mem z)
by exact (p1_meq EE (ss_mem p1_ss0) mem (ms_mem ms1) (spZ regs) ltac:(vm_compute; reflexivity) EE2 HF1).
pose proof (p1_av (w_H W) mem (ms_mem ms1) (spZ regs) MEQ1) as AV1.
assert (W10 : getr (ms_regs ms1) 10 = w64 x).
{ rewrite (p1_RD (w_H W) EE p1_eA ms1 10%bv (SOff 10 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (W1 : getr (ms_regs ms1) 1 = Z_to_bv 64 0x4cd00)
by (rewrite (p1_RD (w_H W) EE p1_eA ms1 1%bv (SLit 0x4cd00) HS1 ltac:(vm_compute; reflexivity)); reflexivity).
(* internal_strlen over the string, which lies outside the window the prologue wrote *)
assert (BYT : forall j, (j <= length s)%nat ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (Z_to_bv 64 (bv_unsigned (w64 x) + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]).
{ intros j Hj. unfold w64. rewrite unsigned_lit_small by lia.
  assert (Hjl : (j < length (s ++ [Z_to_bv 8 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hab j Hjl) as Hv.
  destruct (Hsrc (x + Z.of_nat j) ltac:(lia)) as [_ Hns]. unfold ascratch_stk, ASTACK in Hns.
  rewrite <- (AV1 (x + Z.of_nat j) ltac:(lia) ltac:(lia)) in Hv.
  destruct (sd_rdn1_of_aview (w_H W) (ms_mem ms1) (x + Z.of_nat j) _ Hv) as (b & Hb & Hbv).
  replace (nth j (s ++ [NUL]) NUL) with b; [exact Hb|]. apply bv_eq. rewrite Hbv. reflexivity. }
destruct (RtSIstrlen.tfib_istrlen s (w64 x) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs) (ms_regs ms1) W10 Hnul BYT
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)) as (regs2 & Hms2 & A10 & KEEP2).
apply (sd_call W EE p1_eA ms1 _ 40 (ss_mem p1_eA) 0x4cd00 regs2 _ HS1).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- apply submem_refl.
- vm_compute. reflexivity.
- exact W1.
- apply bv_eq. vm_compute. reflexivity.
- exact Hms2.
- intros r Hr. red in Hr. apply KEEP2; (apply p1_ne_bv5; [lia | vm_compute; lia]).
- intros md2 SBM2 HS2.
set (E1 := havoc EE 40 (map (getr regs2) CLOB)) in HS2.
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs r).
{ intros i r Hi. unfold E1. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (E1_44 : ew E1 44 = w64 len) by (change (ew E1 44) with (getr regs2 10); rewrite A10, <- Hls; reflexivity).
assert (E1_2 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (E1reg 2%nat 2%bv eq_refl); reflexivity).
assert (E1_10 : ew E1 10 = Z_to_bv 64 x) by (rewrite (E1reg 10%nat 10%bv eq_refl); exact G10).
assert (SBM2' : same_but_materialized md md2) by (eapply same_but_materialized_trans; [apply with_vm_backing_same | exact SBM2]).
assert (HSB : st_ok tfibsegs E1 p1_pB (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x4cd00) (ms_mem ms1) (seg_rom tfibsegs)))).
{ unfold p1_pB. apply p1_st_ok_add_fact; [exact HS2 | reflexivity |]. rewrite E1_44. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* 0x4cd00 to the overflow test *)
eapply SRr_bind; [apply (sd_phase W E1 p1_pB _ _ _ _ HSB p1_rC)|].
cbv beta iota. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & _).
assert (MEQ3 : forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (p1_meq E1 (ss_mem p1_pB) _ _ (spZ regs) ltac:(vm_compute; reflexivity) E1_2 HF3 z Hz). exact (MEQ1 z Hz). }
assert (SBM3 : same_but_materialized md (with_vm_backing (m_vm_lazy md2) mat3 md2))
by (eapply same_but_materialized_trans; [exact SBM2' | apply with_vm_backing_same]).
apply (SRr_sym_branch tfibsegs W E1 p1_eC ms3 _ _ BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SOff 44 1) HS3).
{ intros Hc _. exfalso. rewrite (p1_br_ovf E1 10 44 x len E1_10 E1_44 ltac:(lia) ltac:(lia)) in Hc. discriminate. }
intros _ HS3'.
(* to the 64-byte split *)
eapply SRr_bind; [apply (sd_phase W E1 p1_pD _ _ _ _ HS3' p1_rD)|].
cbv beta iota. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & _).
assert (MEQ4 : forall z : word, ~ (spZ regs - 2304 <= bv_unsigned z < spZ regs) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (p1_meq E1 (ss_mem p1_pD) _ _ (spZ regs) ltac:(vm_compute; reflexivity) E1_2 HF4 z Hz). exact (MEQ3 z Hz). }
assert (SBM4 : same_but_materialized md (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat3 md2)) mat4
(with_vm_backing (m_vm_lazy md2) mat3 md2)))
by (eapply same_but_materialized_trans; [exact SBM3 | apply with_vm_backing_same]).
apply (SRr_sym_branch tfibsegs W E1 p1_eD ms4 _ _ BC_GEU (SOff 44 0) (SLit 64) HS4).
+ intros Hc HSb. rewrite (p1_br_len64 E1 44 len E1_44 ltac:(lia)) in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  exact (p1_arm_big B LAWS RGN ly S W regs mem md x len E1 ms4 _ HAR Hal16 Hslo Hshi Hpres G10 Hx Hc Hn32 HRD HROM
  E1reg E1_44 HSb MEQ4 SBM4).
+ intros Hc HSs. rewrite (p1_br_len64 E1 44 len E1_44 ltac:(lia)) in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  exact (p1_arm_small B LAWS ly S W regs mem md x len E1 ms4 _ HAR Hslo Hshi Hpres G10 Hx ltac:(lia) HRD
  E1reg E1_44 HSs MEQ4 SBM4).
Qed.

End p1.
