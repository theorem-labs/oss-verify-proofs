(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0x AFek.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok tfibsegs tbl.
Definition run_postG (W : world tfibsegs) (E : env) (ss ss' : sstate) (st : run_status)
(ms : machine_state) (model : Model) (Q : world tfibsegs -> config -> Prop) : Prop :=
forall ms' mat',
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms')
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms') end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.
Lemma SRr_of_restricted_chainG : forall W E ss ss' st ms msr' model Q,
msteps tfibsegs (restrict (w_H W) ms) msr' ->
match st with RS_ecall => st_ok_ecall tfibsegs E ss' msr' | _ => st_ok tfibsegs E ss' msr' end ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
run_postG W E ss ss' st ms model Q ->
SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W E ss ss' st ms msr' model Q Hms HS' Hfr Hk.
apply (SRr_msteps tfibsegs Hwx_tfa W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as HG. change (ms_mem (restrict (w_H W) ms)) with (mrestrict (w_H W) (ms_mem ms)) in HG.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr'))) with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact HG.
Qed.
Lemma SRr_runG : forall W n E ss ss' st ms model Q,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl n ss = (ss', st) ->
run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_gen tfibsegs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma SRr_run_toG : forall W n stop E ss ss' st ms model Q,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl n stop ss = (ss', st) ->
run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_gen tfibsegs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma SRr_run_shG : forall W n E ss ss' st ms model Q,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN_sh tfibsegs tbl n ss = (ss', st) ->
run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_sh tfibsegs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
End g.
Lemma apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.
Lemma mem_grows_trans' : forall (m1 m2 m3 : word -> option byte), mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 A B x Hx. exact (B x (A x Hx)). Qed.
End d.
Definition X_STEP : sv := Eval vm_compute in sr_get (ss_regs S_HT) 12%bv.
Definition X_FIN : sv := Eval vm_compute in sr_get (ss_regs S_HX) 19%bv.
Definition X_S2 : sv := Eval vm_compute in sr_get (ss_regs S_HX) 18%bv.
Definition DFIN (x : Z) : Z := let a := dh_step x 0 in let b := Z.lxor (Z.shiftr a 47) a in let c := dh_mul b in Z.lxor (Z.shiftr c 47) c.
Lemma shiftr_small0 : forall x k, 0 <= x < 2 ^ k -> 0 <= k -> Z.shiftr x k = 0.
Proof. intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma land_ones_low : forall x k, 0 <= x < 2 ^ k -> 0 <= k -> Z.land x (Z.ones k) = x.
Proof. intros x k Hx Hk. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pin_tag0 : forall E n, bv_unsigned (ew E 11) = n -> 0 <= n < 2 ^ 32 ->
U E (SLit 0) = U E (SAlu ALU_SRL (SOff 11%nat 0) (SLit 32)).
Proof.
intros E n H11 Hn. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11.
unfold zcanon, M64. cbn [zalu_raw]. change (Z.land (32 mod 2 ^ 64) 63) with 32.
rewrite Z.add_0_r, (Z.mod_small n) by lia. rewrite shiftr_small0 by lia. reflexivity.
Qed.
Lemma h0_val : forall E n, bv_unsigned (ew E 11) = n -> 0 <= n < 2 ^ 32 ->
U E (SAlu ALU_XOR (SMd M_MUL (SAlu ALU_AND (SOff 11%nat 0) (SLit 4294967295)) (SLit DH_M8)) (SLit DH_SEED)) = Z.lxor ((n * DH_M8) mod 2 ^ 64) DH_SEED.
Proof.
intros E n H11 Hn. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11.
unfold zcanon, M64. cbn [zalu_raw zmd_raw]. rewrite Z.add_0_r, (Z.mod_small n) by lia.
change (4294967295 mod 2 ^ 64) with (Z.ones 32). rewrite land_ones_low by lia. rewrite (Z.mod_small n) by lia.
rewrite (Z.mod_small DH_M8) by (unfold DH_M8; lia). rewrite (Z.mod_small DH_SEED) by (unfold DH_SEED; lia).
apply Z.mod_small. apply lxor_u64; [apply Z.mod_pos_bound; lia | unfold DH_SEED; lia].
Qed.
Lemma end_val : forall E n buf, bv_unsigned (ew E 11) = n -> 0 <= n < 2 ^ 32 -> bv_unsigned (ew E 10) = buf -> 0 <= buf -> buf + 8 * n < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 10%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 11%nat 0) (SLit 4294967295)) (SLit 3))) = buf + 8 * n.
Proof.
intros E n buf H11 Hn H10 Hb He. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, H10.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small n), (Z.mod_small buf) by lia.
change (4294967295 mod 2 ^ 64) with (Z.ones 32). rewrite land_ones_low by lia. rewrite (Z.mod_small n) by lia.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite (Z.mod_small (n * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma step_val : forall E h w, bv_unsigned (ew E 42) = w -> bv_unsigned (ew E 43) = h -> 0 <= w < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
U E X_STEP = dh_step h w.
Proof.
intros E h w H42 H43 Hw Hh. rewrite U_zev by (vm_compute; reflexivity). unfold X_STEP. cbn [zev svpure]. unfold rho_of. rewrite H42, H43.
unfold zcanon, M64. cbn [zalu_raw zmd_raw]. rewrite !Z.add_0_r. rewrite (Z.mod_small w), (Z.mod_small h) by lia.
rewrite (Z.mod_small 14313749767032793493) by lia. rewrite (Z.mod_small 47) by lia.
rewrite <- (dh_step_zev h w DH_M Hh Hw eq_refl). unfold DH_M. reflexivity.
Qed.
Lemma fin_val : forall E h w, bv_unsigned (ew E 42) = w -> bv_unsigned (ew E 43) = h -> 0 <= w < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
U E X_FIN = DFIN (dh_step h w).
Proof.
intros E h w H42 H43 Hw Hh. rewrite U_zev by (vm_compute; reflexivity). unfold X_FIN. cbn [zev svpure]. unfold rho_of. rewrite H42, H43.
unfold zcanon, M64. cbn [zalu_raw zmd_raw]. rewrite !Z.add_0_r. rewrite (Z.mod_small w), (Z.mod_small h) by lia.
rewrite (Z.mod_small 14313749767032793493) by lia. rewrite (Z.mod_small 47) by lia. rewrite (Z.mod_small 0) by lia.
rewrite (dh_step_zev h w 14313749767032793493 Hh Hw eq_refl). set (x := dh_step h w).
assert (Hx : 0 <= x < 2 ^ 64) by (subst x; apply dh_step_u64).
change (Z.land 47 63) with 47. rewrite !Z.lxor_0_l. rewrite (Z.mod_small x) by exact Hx.
set (a := (x * 14313749767032793493) mod 2 ^ 64). assert (Ha : 0 <= a < 2 ^ 64) by (subst a; apply Z.mod_pos_bound; lia).
pose proof (shiftr_u64 a 47 Ha ltac:(lia)) as Hs. rewrite (Z.mod_small (Z.shiftr a 47)) by exact Hs.
pose proof (lxor_u64 _ _ Hs Ha) as Hb. rewrite (Z.mod_small (Z.lxor (Z.shiftr a 47) a)) by exact Hb.
set (c := (Z.lxor (Z.shiftr a 47) a * 14313749767032793493) mod 2 ^ 64). assert (Hc : 0 <= c < 2 ^ 64) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (shiftr_u64 c 47 Hc ltac:(lia)) as Hs2. rewrite (Z.mod_small (Z.shiftr c 47)) by exact Hs2.
rewrite (Z.mod_small (Z.lxor (Z.shiftr c 47) c)) by (apply lxor_u64; assumption).
unfold DFIN. unfold dh_step, dh_mul. cbn [Z.mul Z.modulo Z.shiftr Z.lxor Z.shiftl].
rewrite Z.lxor_0_l. subst c a. unfold DH_M. reflexivity.
Qed.
Lemma bucket_arith : forall v, 0 <= v < 2 ^ 64 ->
(1605336 + ((v * 2 ^ 44) mod 2 ^ 64 / 2 ^ 42) mod 2 ^ 64) mod 2 ^ 64 = 1605336 + 4 * (v mod 2 ^ 20).
Proof.
intros v Hv.
change (2 ^ 44) with 17592186044416. change (2 ^ 42) with 4398046511104. change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 20) with 1048576.
pose proof (Z.mod_pos_bound v 1048576 ltac:(lia)) as R. pose proof (Z.div_mod v 1048576 ltac:(lia)) as D.
set (q := v / 1048576) in *. set (r := v mod 1048576) in *. clearbody q r.
assert (E1 : v * 17592186044416 = r * 17592186044416 + q * 18446744073709551616) by lia.
rewrite E1, Z.mod_add by lia. rewrite (Z.mod_small (r * 17592186044416)); [| clear - R; lia].
replace (r * 17592186044416) with (4 * r * 4398046511104) by (clear; lia). rewrite Z.div_mul by (clear; lia).
rewrite (Z.mod_small (4 * r)) by (clear - R; lia). apply Z.mod_small. clear - R; lia.
Qed.
Lemma s2_of_fin : forall E, U E X_S2 = 1605336 + 4 * ((U E X_FIN) mod 2 ^ 20).
Proof.
intros E. rewrite !U_zev by (vm_compute; reflexivity). unfold X_S2, X_FIN. cbn [zev svpure].
match goal with |- context [zalu_raw 63 64 ALU_SLL ?f _] => set (v := f) end.
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; unfold zcanon, M64; apply Z.mod_pos_bound; lia). clearbody v.
unfold zcanon, M64. cbn [zalu_raw]. change (Z.land (44 mod 2 ^ 64) 63) with 44. change (Z.land (42 mod 2 ^ 64) 63) with 42.
rewrite (Z.mod_small 1605336) by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply bucket_arith. exact Hv.
Qed.
Lemma hd_and_val : forall E v, bv_unsigned (ew E 38) = v -> 0 <= v < 2 ^ 31 ->
U E (SAlu ALU_AND (SOff 38%nat 0) (SLit 2147483647)) = v.
Proof.
intros E v H38 Hv. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H38.
unfold zcanon, M64. cbn [zalu_raw]. rewrite Z.add_0_r, (Z.mod_small v) by lia.
change (2147483647 mod 2 ^ 64) with (Z.ones 31). rewrite land_ones_low by lia. apply Z.mod_small. lia.
Qed.
Lemma hd_and_val0 : forall E v, bv_unsigned (ew E 38) = v -> 0 <= v < 2 ^ 31 ->
U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 38%nat 0) (SLit 2147483647)) (SLit 0)) = v.
Proof.
intros E v H38 Hv. rewrite U_SAlu, (hd_and_val E v H38 Hv), U_SLit. unfold zcanon, M64. cbn [zalu_raw]. rewrite (Z.mod_small 0), Z.add_0_r by lia.
apply Z.mod_small. lia.
Qed.
Lemma map1_valw : forall E v, bv_unsigned (ew E 42) = v -> 0 <= v < 65536 ->
U E (SAlu ALU_ADD (SLit 5799656) (SAlu ALU_SLL (SAluw ALU_SRL (SOff 42%nat 0) (SLit 16)) (SLit 3))) = 5799656.
Proof.
intros E v H42 Hv. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H42.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r. rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small v) by lia.
change (Z.land ((16 mod 2 ^ 64) mod 2 ^ 32) 31) with 16. rewrite (shiftr_small0 v 16) by lia. vm_compute. reflexivity.
Qed.
Lemma map1_val1 : forall E n, bv_unsigned (ew E 35) = n -> 0 <= n + 1 < 65536 ->
U E (SAlu ALU_ADD (SLit 5799656) (SAlu ALU_SLL (SAlu ALU_SRL (SOff 35%nat 1) (SLit 16)) (SLit 3))) = 5799656.
Proof.
intros E n H35 Hn. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H35.
unfold zcanon, M64. cbn [zalu_raw]. rewrite ?Z.add_0_r. rewrite (Z.mod_small (n + 1)) by lia. change (Z.land (16 mod 2 ^ 64) 63) with 16.
rewrite (shiftr_small0 (n + 1) 16) by lia. vm_compute. reflexivity.
Qed.
Lemma node_val : forall E nb v, bv_unsigned (ew E 32) = nb -> bv_unsigned (ew E 42) = v -> 0 <= v < 65536 -> 0 <= nb -> nb + 16 * 65536 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 42%nat 0) (SLit 65535)) (SLit 4))) = nb + 16 * v.
Proof.
intros E nb v H32 H42 Hv Hnb Hh. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H32, H42.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small v), (Z.mod_small nb) by lia.
change (65535 mod 2 ^ 64) with (Z.ones 16). rewrite land_ones_low by lia. rewrite (Z.mod_small v) by lia.
change (Z.land (4 mod 2 ^ 64) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (Z.mod_small (v * 16)) by lia. rewrite (Z.mod_small (nb + v * 16)) by lia. lia.
Qed.
Lemma node_val1 : forall E nb n k, bv_unsigned (ew E 32) = nb -> bv_unsigned (ew E 35) = n -> 0 <= n + 1 < 65536 -> 0 <= nb -> nb + 16 * 65536 < 2 ^ 64 -> (k <= 2)%nat ->
U E (Nat.iter k (fun e => SAlu ALU_ADD e (SLit 0)) (SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 35%nat 1) (SLit 65535)) (SLit 4)))) = nb + 16 * (n + 1).
Proof.
intros E nb n k H32 H35 Hn Hnb Hh Hk.
assert (B : U E (SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 35%nat 1) (SLit 65535)) (SLit 4))) = nb + 16 * (n + 1)).
{ rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H32, H35.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small (n + 1)), (Z.mod_small nb) by lia.
change (65535 mod 2 ^ 64) with (Z.ones 16). rewrite land_ones_low by lia. rewrite (Z.mod_small (n + 1)) by lia.
change (Z.land (4 mod 2 ^ 64) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (Z.mod_small ((n + 1) * 16)) by lia. rewrite Z.mod_small by lia. lia. }
assert (Z0 : forall e, U E e = nb + 16 * (n + 1) -> U E (SAlu ALU_ADD e (SLit 0)) = nb + 16 * (n + 1)).
{ intros e He. rewrite U_SAlu, He, U_SLit. unfold zcanon, M64. cbn [zalu_raw]. rewrite (Z.mod_small 0), Z.add_0_r by lia. apply Z.mod_small. lia. }
destruct k as [|[|[|k]]]; cbn [Nat.iter]; [exact B | apply Z0; exact B | apply Z0; apply Z0; exact B | lia].
Qed.
Lemma or_tag_val : forall E n, bv_unsigned (ew E 11) = n -> 0 <= n < 2 ^ 32 ->
U E (SOff 11%nat 0) = U E (SAlu ALU_OR (SOff 11%nat 0) (SAlu ALU_SRL (SOff 11%nat 0) (SLit 32))).
Proof.
intros E n H11 Hn. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, !(Z.mod_small n) by lia. change (Z.land (32 mod 2 ^ 64) 63) with 32.
rewrite (shiftr_small0 n 32) by lia. rewrite (Z.mod_small 0), Z.lor_0_r by lia. rewrite ?(Z.mod_small n) by lia. reflexivity.
Qed.
Lemma t0_val : forall E t, bv_unsigned (ew E 34) = t -> 0 <= t < 2 ^ 20 -> U E (SLit 0) = U E (SAlu ALU_SRL (SOff 34%nat 0) (SLit 20)).
Proof.
intros E t H34 Ht. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t) by lia. change (Z.land (20 mod 2 ^ 64) 63) with 20.
rewrite (shiftr_small0 t 20) by lia. reflexivity.
Qed.
Lemma t1_val : forall E n t, bv_unsigned (ew E 11) = n -> bv_unsigned (ew E 34) = t -> 0 <= n -> 0 <= t -> n + t < 2 ^ 20 ->
U E (SLit 0) = U E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 11%nat 0) (SOff 34%nat 0)) (SLit 20)).
Proof.
intros E n t H11 H34 Hn Ht Hs. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t), (Z.mod_small n), (Z.mod_small (n + t)) by lia. change (Z.land (20 mod 2 ^ 64) 63) with 20.
rewrite (shiftr_small0 (n + t) 20) by lia. reflexivity.
Qed.
Lemma t32_val : forall E t, bv_unsigned (ew E 34) = t -> 0 <= t < 2 ^ 32 -> U E (SAlu ALU_SRL (SOff 34%nat 0) (SLit 32)) = U E (SLit 0).
Proof.
intros E t H34 Ht. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t) by lia. change (Z.land (32 mod 2 ^ 64) 63) with 32.
rewrite (shiftr_small0 t 32) by lia. reflexivity.
Qed.
Lemma slot_val : forall E sb t, bv_unsigned (ew E 33) = sb -> bv_unsigned (ew E 34) = t -> 0 <= t < 2 ^ 20 -> 0 <= sb -> sb + 8 * 2 ^ 20 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 33%nat 0) (SAlu ALU_SLL (SOff 34%nat 0) (SLit 3))) = sb + 8 * t.
Proof.
intros E sb t H33 H34 Ht Hsb Hh. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H33, H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t), (Z.mod_small sb) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mod_small (t * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mcend_val : forall E n sl, bv_unsigned (ew E 11) = n -> bv_unsigned (ew E 41) = sl -> 0 <= n < 2 ^ 32 -> 0 <= sl -> sl + 8 + 8 * n < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 11%nat 0) (SLit 3)) (SLit 8)) (SOff 41%nat 0)) = sl + 8 + 8 * n.
Proof.
intros E n sl H11 H41 Hn Hsl Hh. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, H41.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small n), (Z.mod_small sl) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mod_small (n * 8)), (Z.mod_small 8) by lia. rewrite (Z.mod_small (n * 8 + 8)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma std_val : forall E t, bv_unsigned (ew E 34) = t -> 0 <= t < 2 ^ 17 ->
U E (SLit 1539808) = U E (SAlu ALU_ADD (SAlu ALU_ADD (SLit 1539784) (SAlu ALU_AND (SAlu ALU_SRL (SOff 34%nat 0) (SLit 16)) (SLit (-16)))) (SLit 24)).
Proof.
intros E t H34 Ht. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t) by lia. change (Z.land (16 mod 2 ^ 64) 63) with 16.
rewrite Z.shiftr_div_pow2 by lia.
assert (C : t / 2 ^ 16 = 0 \/ t / 2 ^ 16 = 1).
{ change (2 ^ 16) with 65536. change (2 ^ 17) with 131072 in Ht. destruct (Z_lt_le_dec t 65536); [left; apply Z.div_small; lia | right].
symmetry. apply Z.div_unique with (r := t - 65536); [left; lia | lia]. }
assert (X : Z.land ((t / 2 ^ 16) mod 2 ^ 64) ((-16) mod 2 ^ 64) = 0) by (destruct C as [-> | ->]; vm_compute; reflexivity).
rewrite X. vm_compute. reflexivity.
Qed.
Lemma ne_refute : forall E a b, U E a = U E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = true -> False.
Proof.
intros E a b HU Hb. unfold branch_taken, bv_eqb in Hb. unfold U in HU.
assert (E2 : sv_denot E a = sv_denot E b) by (apply bv_eq; exact HU). rewrite E2, Z.eqb_refl in Hb. discriminate Hb.
Qed.
Lemma eq_refute : forall E a b, U E a = U E b -> branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false -> False.
Proof.
intros E a b HU Hb. unfold branch_taken, bv_eqb in Hb. unfold U in HU.
assert (E2 : sv_denot E a = sv_denot E b) by (apply bv_eq; exact HU). rewrite E2, Z.eqb_refl in Hb. discriminate Hb.
Qed.
Lemma tot_val : forall E n t, bv_unsigned (ew E 11) = n -> bv_unsigned (ew E 34) = t -> 0 <= n -> 0 <= t -> n + 1 + t < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 11%nat 1) (SOff 34%nat 0)) = t + n + 1.
Proof.
intros E n t H11 H34 Hn Ht Hs. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, H34.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t), (Z.mod_small (n + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End i.
Ltac srr_after_runG HS :=
let ms' := fresh "ms" in let mat' := fresh "mat" in
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' mat' HS HF HG;
cbn [ms_mem mkst] in HF, HG;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac srr_runG tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_runG tbl tblok W FUEL E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
srr_after_runG HS
end
end
| _ => fail "srr_runG: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_run_toG tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_run_toG tbl tblok W FUEL stop E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
cbv beta iota;
srr_after_runG HS
end
end
| _ => fail "srr_run_toG: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac srr_run_shG tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN_sh segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_sh segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_run_shG tbl tblok W FUEL E ss ss' st ms _ _ HS Hrun);
clear Hrun HS;
srr_after_runG HS
end
end
| _ => fail "srr_run_shG: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
