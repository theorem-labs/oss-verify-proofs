(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0z.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL17.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL18.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL19.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma driver_tail_short_eq : forall data buf cap s,
dlen data < HDR_MIN -> driver_tail data (RdLoaded buf cap) s = ret DL_short s.
Proof. intros data buf cap s H. unfold driver_tail. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma driver_tail_overrun_eq : forall data buf cap s,
HDR_MIN <= dlen data -> dlen data < HDR_MIN + config_len data ->
driver_tail data (RdLoaded buf cap) s = ret DL_overrun s.
Proof.
intros data buf cap s H1 H2. unfold driver_tail.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.
Lemma driver_tail_run_eq : forall data buf cap s,
HDR_MIN <= dlen data -> HDR_MIN + config_len data <= dlen data -> payload_len data = 0 ->
driver_tail data (RdLoaded buf cap) s = ret (DL_run buf cap None) s.
Proof.
intros data buf cap s H1 H2 H3. unfold driver_tail.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), (proj2 (Z.eqb_eq _ _) H3). reflexivity.
Qed.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis LIBX : lib_contract_x_all src0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis FRM : frm_zero fp_csr.
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Variable RBD : rbound.
Hypothesis ROOMX : room_calls (payload_len data) (calls data) RBD.
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis Hsp47 : bv_unsigned sp <= 2 ^ 47.
Lemma run_from_QX : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms ->
aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (fun r => res_ok (snd r) RBD) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HT HS HMR Hmd HD HJ HG HL HK.
pose proof (config_len_bound data) as Hclb.
destruct (Z.eq_dec (payload_len data) 0) as [Hpl0 | Hplnz].
-
pose proof (res_of_tail_none (fun r => res_ok (snd r) RBD) data b0 cap0 A' HL Hok Hpl0) as HRb. cbn [snd] in HRb.
rewrite (driver_tail_run_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret (DL_run b0 cap0 None) A') K) with (K (DL_run b0 cap0 None, A')).
apply (rz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_run b0 cap0 None, A')) _); [| apply t_eq_sym; apply HK].
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (src0_runX_0E1 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok Hz Hc Hpl0 E ms _ RBD HE HT HS HMR Hmd HRb ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX])).
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (src0_runX_1E1 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ RBD HE HT HS HMR Hmd HRb ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX])).
* exact (src0_runX_1E2 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ RBD HE HT HS HMR Hmd HRb ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX])).
* exact (src0_runX_1E3 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ RBD HE HT HS HMR Hmd HRb ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX])).
* exact (src0_runX_1E4 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ RBD HE HT HS HMR Hmd HRb ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX])).
-
assert (Hpl : 0 < payload_len data) by (unfold payload_len, HDR_MIN in *; lia).
assert (Heq := driver_tail_loaded_eq data b0 cap0 A'
ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.eqb_neq; exact Hplnz)).
rewrite (tset_bind_eq _ _ _ _ _ Heq).
pose proof (jinv_head_eq _ _ _ _ _ Heq HJ) as HJ'. pose proof (gtree_head_eq _ _ _ _ _ Heq HG) as HG'.
pose proof (res_of_tail_some (fun r => res_ok (snd r) RBD) data b0 cap0 A' HL Hok Hplnz) as HRb.
assert (HRb' : forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> res_ok A2 RBD)
by (intros tr q A2 Hp; exact (HRb tr (Some q, A2) Hp)).
assert (HK' : forall r : option sptr * astate,
t_eq (tset (let '(a, s') := r in payload_k b0 cap0 a s') K) (leaf_shapeX data (in_fs inp) (payload_leaf b0 cap0 r))).
{ intros [[q|] s']; cbn [payload_k payload_leaf fst snd]; apply HK. }
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (src0_runX_0M1 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ RBD HE HT HS HMR Hmd HD HRb' ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX]) _ HJ' HG' HK').
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (src0_runX_1M1 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ RBD HE HT HS HMR Hmd HD HRb' ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX]) _ HJ' HG' HK').
* exact (src0_runX_1M2 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ RBD HE HT HS HMR Hmd HD HRb' ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX]) _ HJ' HG' HK').
* exact (src0_runX_1M3 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ RBD HE HT HS HMR Hmd HD HRb' ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX]) _ HJ' HG' HK').
* exact (src0_runX_1M4 API AX LIBX FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ RBD HE HT HS HMR Hmd HD HRb' ltac:(first [exact ROOMX | rewrite <- Hc in ROOMX; exact ROOMX]) _ HJ' HG' HK').
Qed.
Lemma post_from_h1X : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (fun r => res_ok (snd r) RBD) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
pose proof (config_len_bound data) as Hclb.
apply (src0_to_P API AX data cap0 L' A' b0 E md Hub Hcap0 HE HAN ms _ Hok HLc HS HMR HD).
intros ms3 HS3 HMR3 HD3. clear HS HMR HD.
destruct HE as (HEd & HE13 & HE26).
assert (HRE : run_env (E_P E data (ptr_addr L' b0 + 2 + config_len data)) data (ptr_addr L' b0)).
{ unfold run_env. split; [| split; [| split; [| split]]].
- rewrite E_P_ed by lia. exact HEd.
- rewrite E_P_old by lia. exact HE13.
- rewrite E_P_old by lia. exact HE26.
- apply E_P_46. lia.
- apply (hdr_anch_ext E _ HAN). intros n Hn. apply E_P_old. lia. }
assert (HTE : env_top (E_P E data (ptr_addr L' b0 + 2 + config_len data))) by (unfold env_top; rewrite E_P_old by lia; exact HT).
apply (src0_P_to_QX API AX data cap0 L' A' b0 md Hub Hok HLc _ ms3 _ HRE HS3 HMR3 HD3).
intros ms4 HS4 HMR4 HD4. clear HS3 HMR3 HD3.
exact (run_from_QX cap0 L' A' b0 _ ms4 md K Hub Hcap0 HW HB Hid Hok HLc HRE HTE HS4 HMR4 Hmd HD4 HJ HG HL HK).
Qed.
Lemma post_from_h0X : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (fun r => res_ok (snd r) RBD) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HLc HE HAN HT HS HMR Hmd0 HD HJ HG HL HK.
pose proof (md_invX_inv _ _ Hmd0 : md_ok inp md) as Hmd.
pose proof (config_len_bound data) as Hclb.
assert (Hnn : 0 <= dlen data) by (unfold dlen; lia).
destruct (Z_lt_le_dec (dlen data) 6) as [Hshort | Hhdr].
-
rewrite (driver_tail_short_eq data b0 cap0 A') by (unfold HDR_MIN; exact Hshort).
change (tset (ret DL_short A') K) with (K (DL_short, A')).
apply (rz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_short, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX leaf_shape fst].
exact (src0_short_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms md HE HAN ltac:(lia) HS HMR Hmd).
-
apply (src0_to_h1 API AX data cap0 L' A' b0 Hub Hcap0 HLc E ms md _ HE HAN Hhdr HS HMR HD).
intros ms2 HS2 HMR2 HD2. clear HS HMR HD.
destruct (Z_lt_le_dec (dlen data) (6 + config_len data)) as [Hov | Hok].
+
rewrite (driver_tail_overrun_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret DL_overrun A') K) with (K (DL_overrun, A')).
apply (rz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_overrun, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX leaf_shape fst].
exact (src0_overrun_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms2 md HE HAN Hhdr Hov HS2 HMR2 Hmd).
+ exact (post_from_h1X cap0 L' A' b0 E ms2 md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HT HS2 HMR2 Hmd0 HD2 HJ HG HL HK).
Qed.
Theorem src0_postX : forall K : dleaf * astate -> TSet,
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST API sp tid a0 path inp data rnd (fun r => res_ok (snd r) RBD) K.
Proof.
intros K HK. unfold POST. cbv zeta beta.
intros cap' bufp' A' Lc' J' g' len0 w ms' md' HLc Hcap Hlen0 Hub HW HB Hid HS Hw HL0 HMR Hmd0 HD HJ HG HL.
pose proof (md_invX_of_post inp md' Hvfs Hmd0) as Hmd.
unfold MAX_INPUT in Hcap. subst len0.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp', cap') (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc' A' (ms_mem ms') md' bufp' cap' 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
lazymatch type of HS with st_ok _ ?E0 _ _ => set (E := E0) in HS end.
assert (HE : hdr_env E data (ptr_addr Lc' bufp')).
{ subst E. unfold hdr_env. split; [| split].
- rewrite ed_ewset. apply ed_lp2.
- rewrite ew_ewset_other by lia. unfold E_lp. rewrite ew_ewset_other, ew_ewset_other, ew_ewset_other, ew_ewset_same by lia.
apply u64_of_Z. lia.
- rewrite ew_ewset_other by lia. unfold E_lp. rewrite ew_ewset_other, ew_ewset_same by lia.
apply u64_of_Z. unfold dlen in HLc. lia. }
assert (HAN : hdr_anch E).
{ intros G HGa. subst E. apply (anch_lp sp tid a0 path inp data rnd HSA0 J' (ptr_addr Lc' bufp') g' (Z.of_nat (length data)) cap' _ G); [| exact HGa].
apply (ext29_ewset data); [lia | apply ext29_refl]. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E ss_h0 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX Lc' A' m0 m1 _ E (ss_facts ss_h0) src0_keep rs0 bufp' cap' (ptr_addr Lc' bufp') data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(unfold dlen in HLc; lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (HT : env_top E) by (subst E; unfold env_top; rewrite ew_ewset_other by lia; rewrite ew_lp; cbn; exact Hsp47);
exact (post_from_h0X cap' Lc' A' bufp' E msx md' K Hub ltac:(lia) HW HB Hid HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK) end.
Qed.
End c.
End b.
