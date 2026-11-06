(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFeq.v, with its module paths changed; 405 of its 438 lines of code are new or changed and 214 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDMallocBody.v, with its module paths, module names and numbers changed; 342 of its 445 lines of code are new or changed and 335 lines of the source are left out. *)
(* The second stretch of plugin-hostd/fuzz_command's strdup entry ___interceptor_strdup 0x4ccb0: from the join of
   the two shadow-check arms 0x4cd64 to the call of __asan::asan_malloc 0x34528.

     4cd64 addi a0,s0,-2048; addi a0,a0,-96; addi s5,a0,2047; sd zero,9(s5)   top_frame_bp = 0 at sp0-88
     4cd74 sd s7,0(s6); sd zero,8(s6)        trace = sp0-2128, size = 0, tag = 0
     4cd7c jal 603c8; li a1,2; bltu a1,a0,4cdcc     GetMallocContextSize = [0xb1dbc] = 30
     4cdcc jal 78e88                                GetCurrentPc = 0x4cdd0
     4cdd0 auipc a1; ld a1,1552(a1); lbu s4,34(a1)  fast_unwind_on_malloc = 1
     4cddc mv s3,a0; jal 603c8; mv a5,a0; seqz/addi/and; li a0,1; sd a1,9(s5); bltu a0,a5,4ce70
     4ce70 a0 = sp0-2144, a1 = 0x4cdd0, a2 = s0 = sp0, a3 = 0, a4 = 1; jal 603d8   (AFl0.v tfib_unwind_spec)
     4ce8c a1 = sp0-2144; a0 = s2; jal 34528

   The symbolic run is over the entry's own table (RtDStrdupD.v tbl_sd) from a state whose one stack region is the
   trace object [sp0-2144, sp0-80); the unwinder is crossed with its call spec, and after it the state keeps no
   region, because the three instructions before the call of asan_malloc touch no memory. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YO0d YN2j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtAPI RtDDefs RtDStrdupD RtDMallocLeaf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtDMallocUnw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* The state at 0x4cd64: s0 = sp0 = atom 2 + 2144, s6 = atom 2, s7 = atom 2 + 16; the stack region is the trace
   object [atom 2, atom 2 + 2064), the only bytes this stretch writes. *)
Definition p2_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 2064 0 2064 [].
Definition p2_regs : list sv := sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 2 2144)) 22%bv (SOff 2 0)) 23%bv (SOff 2 16).
Definition p2_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 43) (2 ^ 47) 4)] [] [].
Definition P2_SS0 : sstate := mkSS 0x4cd64 p2_regs (p2_stk :: map ro_region sd_rodata) None p2_facts.
Definition P2_U : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_sd FUEL 0x603d8 P2_SS0).
Definition P2_HAV : nat := 64.
Definition P2_1 : sstate := Eval vm_compute in ss_after_call P2_U [] P2_HAV 0x4ce8c.
Definition P2_A : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_sd FUEL 0x34528 P2_1).
Definition p2_u_r0 : YP09.region := Eval vm_compute in hd p2_stk (ss_mem P2_U).

Lemma p2_run_u : sym_run_toN tfibsegs tbl_sd FUEL 0x603d8 P2_SS0 = (P2_U, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma p2_run_a : sym_run_toN tfibsegs tbl_sd FUEL 0x34528 P2_1 = (P2_A, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma p2_1_eq : ss_after_call P2_U [] P2_HAV 0x4ce8c = P2_1.
Proof. vm_compute. reflexivity. Qed.
Lemma p2_1_mem : ss_mem P2_1 = [].
Proof. vm_compute. reflexivity. Qed.
Lemma p2_win0 : forallb (fun t => win_eqb t (Some 2%nat, 0, 2064) || (snd t <=? snd (fst t))) (windows (ss_mem P2_SS0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p2_u_atoms : ss_atoms_lt P2_HAV P2_U = true /\ regions_wf [] = true /\ no_cdata [] = true /\ mem_atoms_lt P2_HAV [] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma p2_submem : submem [] (ss_mem P2_U).
Proof. apply submemb_sound. vm_compute. reflexivity. Qed.
Lemma p2_u_mem0 : nth_error (ss_mem P2_U) 0 = Some p2_u_r0.
Proof. vm_compute. reflexivity. Qed.
Lemma p2_u_r0_shape :
YP09.r_base p2_u_r0 = Some 2%nat /\ YP09.r_wlo p2_u_r0 = 0 /\ YP09.r_whi p2_u_r0 = 2064 /\
nth_error (YP09.r_chunks p2_u_r0) 1 = Some (YP09.mkChunk 8 (CVal 8 (SLit 0))) /\
nth_error (YP09.r_chunks p2_u_r0) 2 = Some (YP09.mkChunk 0 (CVal 8 (SOff 2 16))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma p2_u_shape :
ss_pc P2_U = 0x603d8 /\ ss_resv P2_U = None /\
sr_get (ss_regs P2_U) 1%bv = SLit 0x4ce8c /\
sr_get (ss_regs P2_U) 2%bv = SOff 2 0 /\
sr_get (ss_regs P2_U) 4%bv = SOff 4 0 /\
sr_get (ss_regs P2_U) 10%bv = SOff 2 0 /\
sr_get (ss_regs P2_U) 11%bv = SLit 0x4cdd0 /\
sr_get (ss_regs P2_U) 12%bv = SOff 2 2144 /\
sr_get (ss_regs P2_U) 13%bv = SLit 0 /\
sr_get (ss_regs P2_U) 14%bv = SLit 1 /\
sr_get (ss_regs P2_U) 15%bv = SLit 30.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma p2_a_shape :
ss_pc P2_A = 0x34528 /\ ss_resv P2_A = None /\
sr_get (ss_regs P2_A) 1%bv = SLit 0x4ce9c /\
sr_get (ss_regs P2_A) 2%bv = SOff 2 0 /\
sr_get (ss_regs P2_A) 3%bv = SOff 3 0 /\
sr_get (ss_regs P2_A) 4%bv = SOff 4 0 /\
sr_get (ss_regs P2_A) 8%bv = SOff 2 2144 /\
sr_get (ss_regs P2_A) 9%bv = SOff 9 0 /\
sr_get (ss_regs P2_A) 10%bv = SOff 18 0 /\
sr_get (ss_regs P2_A) 11%bv = SOff 2 0 /\
sr_get (ss_regs P2_A) 18%bv = SOff 18 0 /\
sr_get (ss_regs P2_A) 22%bv = SOff 2 0 /\
sr_get (ss_regs P2_A) 23%bv = SOff 2 16 /\
sr_get (ss_regs P2_A) 24%bv = SOff 24 0 /\
sr_get (ss_regs P2_A) 25%bv = SOff 25 0 /\
sr_get (ss_regs P2_A) 26%bv = SOff 26 0 /\
sr_get (ss_regs P2_A) 27%bv = SOff 27 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section p2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition sd_trace (ly : alayout) (sp0 ra0 nfp0 : Z) (ch : list (Z * Z * Z)) : list Z :=
if sp0 + 16 <? ly_top ly then unwind_of_chain PC_STRDUP_RA0 ((sp0, ra0, nfp0) :: ch) else [PC_STRDUP_RA0].

Definition sd_p2_post (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 n : Z)
(mem : word -> option byte) (md : Model) (regs : bvmap 5 word) (ra0 nfp0 : Z) (ch : list (Z * Z * Z)) :
world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs2 mem2 md2,
c' = cfg_at tfibsegs 0x34528 regs2 mem2 md2 /\
AR tfibsegs B ly S W mem2 md2 /\ same_but_materialized md md2 /\
getr regs2 1 = w64 0x4ce9c /\ getr regs2 2 = w64 (sp0 - 2144) /\
getr regs2 10 = w64 n /\ getr regs2 11 = w64 (sp0 - 2144) /\
getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
getr regs2 8 = getr regs 8 /\ getr regs2 9 = getr regs 9 /\ getr regs2 18 = getr regs 18 /\
(forall r : bv 5, 22 <= bv_unsigned r <= 27 -> getr regs2 r = getr regs r) /\
astrace_at tfibsegs W mem2 (sp0 - 2144) (sd_trace ly sp0 ra0 nfp0 ch) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2304 <= a < sp0 - 80) ->
aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a).

(* a register of a symbolic state: an atom plus an offset, or a literal *)
Lemma p2_reg_off : forall H E ss ms (r : bv 5) k off,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k off ->
getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E k) + off).
Proof. intros H E ss ms r k off HS Hr. rewrite (st_ok_reg_denot H E ss ms r HS), Hr. reflexivity. Qed.
Lemma p2_reg_atom : forall H E ss ms (r : bv 5) k,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k 0 -> getr (ms_regs ms) r = ew E k.
Proof.
intros H E ss ms r k HS Hr. rewrite (p2_reg_off H E ss ms r k 0 HS Hr), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma p2_reg_lit : forall H E ss ms (r : bv 5) z,
st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros H E ss ms r z HS Hr. rewrite (st_ok_reg_denot H E ss ms r HS), Hr. reflexivity. Qed.

(* every frame of the trace is a word *)
Lemma p2_trace_bound : forall ly sp0 ra0 nfp0 ch,
0 <= ra0 < 2 ^ 64 -> Forall (fun r => 0 <= snd (fst r) < 2 ^ 64) ch ->
forall x, In x (sd_trace ly sp0 ra0 nfp0 ch) -> 0 <= x < 2 ^ 64.
Proof.
intros ly sp0 ra0 nfp0 ch Hra HF x Hx.
assert (Hp : 0 <= PC_STRDUP_RA0 < 2 ^ 64) by (unfold PC_STRDUP_RA0; lia).
assert (FI : forall (l : list Z) y, In y (firstn kUnwindMax l) -> In y l)
by (intros l y Hy; rewrite <- (firstn_skipn kUnwindMax l); apply in_or_app; left; exact Hy).
unfold sd_trace in Hx. destruct (sp0 + 16 <? ly_top ly); [|destruct Hx as [<-|[]]; exact Hp].
unfold unwind_of_chain in Hx. apply FI in Hx.
destruct Hx as [<-|Hx']; [exact Hp|].
apply in_flat_map in Hx' as ([[fp ra] nfp] & Hin & Hx').
destruct (ra =? PC_STRDUP_RA0); [destruct Hx'|]. destruct Hx' as [<-|[]].
destruct Hin as [Heq|Hin].
- injection Heq as _ <- _. exact Hra.
- exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.

Theorem sd_p2_srr : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B -> tfib_unwind_spec ->
forall ly S (W : world tfibsegs) regs mem md (sp0 xs n ra0 nfp0 : Z) (ch : list (Z * Z * Z)),
AR tfibsegs B ly S W mem md ->
2 ^ 44 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
ly_stk_lo ly + ASTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
rdword (aview tfibsegs (w_H W) mem) (sp0 - 8) = Some ra0 ->
rdword (aview tfibsegs (w_H W) mem) (sp0 - 16) = Some nfp0 ->
4096 <= ra0 ->
(if sp0 + 16 <? ly_top ly
 then (if bad_next sp0 (ly_top ly) nfp0 then ch = []
       else sp0 + 16 <= nfp0 /\ fpchain (rdword (aview tfibsegs (w_H W) mem)) nfp0 (ly_top ly) ch)
 else ch = []) ->
getr regs 2 = w64 (sp0 - 2144) -> getr regs 8 = w64 sp0 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 xs -> getr regs 18 = w64 n -> 0 < n < 2 ^ 32 ->
getr regs 22 = w64 (sp0 - 2144) -> getr regs 23 = w64 (sp0 - 2128) ->
spZ regs = sp0 - 2144 ->
SRr tfibsegs W (cfg_at tfibsegs 0x4cd64 regs mem md) (sd_p2_post B ly S W sp0 n mem md regs ra0 nfp0 ch).
Proof.
intros B LAWS TB UNWIND ly S W regs mem md sp0 xs n ra0 nfp0 ch HAR Hsp Hal Hslo Hbot Hshi Hpres Hra0 Hnfp0 Hra4096 Hch
G2 G8 G3 G4 G9 G18 Hn G22 G23 Hspz.
pose proof (am_layout B ly S _ (proj1 HAR)) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ (proj1 HAR)); exact (ts_tsd B TB)).
pose proof (lo_top ly LY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, Hpres.
pose proof ASAN_CEIL_range as [CR _]. pose proof (lo_stk_ceil ly LY) as Lceil.
pose proof (RtDMallocUnw.T_high ly LY) as (T1 & T2). pose proof (RtDMallocUnw.C_high ly LY) as (C1 & C2).
unfold kThreadObjSize, kLowShadowBeg, kHighMemBeg in T2, C2.
assert (TLO : ly_T ly + 4096 <= ly_stk_lo ly) by lia.
assert (CLO : ly_C ly + 256 <= ly_stk_lo ly) by lia.
assert (Hal8 : sp0 mod 8 = 0).
{ replace sp0 with (2 * (sp0 / 16) * 8 + sp0 mod 16) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
rewrite Hal, Z.add_0_r. apply Z_mod_mult. }
set (Hd := w_H W) in *.
(* ---- the facts the unwinder reads, at 0x4cd64 ---- *)
set (m0 := mrestrict Hd mem).
assert (V1 : val_mem tfibsegs m0 0xb1d98 1 1) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb1d98 1 1 (proj1 HAR)); vm_compute; reflexivity).
assert (V2 : val_mem tfibsegs m0 0xb0920 1 1) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb0920 1 1 (proj1 HAR)); vm_compute; reflexivity).
assert (V3 : val_mem tfibsegs m0 0xb0924 4 0) by (apply (tfib_const_lookup B TB ly S Hd mem 0xb0924 4 0 (proj1 HAR)); vm_compute; reflexivity).
assert (V11 : val_mem tfibsegs m0 0xa63d0 8 0x140b60) by (apply (tfib_const_lookup B TB ly S Hd mem 0xa63d0 8 0x140b60 (proj1 HAR)); vm_compute; reflexivity).
assert (V12 : val_mem tfibsegs m0 0x140b60 8 4096) by (apply (tfib_const_lookup B TB ly S Hd mem 0x140b60 8 4096 (proj1 HAR)); vm_compute; reflexivity).
assert (V4 : val_mem tfibsegs m0 (TFIB_TP - 88) 8 TFIB_TSD).
{ replace (TFIB_TP - 88) with (aeval B ly (ATp (-88))) by (cbn [aeval]; rewrite (ts_tp B TB); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn [aeval]; rewrite HTSD; unfold TFIB_TSD; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (ATp (-88)) 8 (ATsd 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V5 : val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly)).
{ replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn [aeval]; rewrite HTSD; unfold TFIB_TSD; lia).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (ATsd 0) 8 (AC 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V6 : val_mem tfibsegs m0 (ly_C ly + 152) 8 (ly_T ly)).
{ replace (ly_C ly + 152) with (aeval B ly (AC 152)) by (cbn [aeval]; lia).
replace (ly_T ly) with (aeval B ly (AT 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AC 152) 8 (AT 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V7 : val_mem tfibsegs m0 (ly_T ly + 40) 1 0).
{ replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 40) 1 (ANum 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V8 : val_mem tfibsegs m0 (ly_T ly + 8) 8 (ly_top ly)).
{ replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn [aeval]; lia).
replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn [aeval]; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 8) 8 (ATop 0) (proj1 HAR)). vm_compute. reflexivity. }
assert (V9 : val_mem tfibsegs m0 (ly_T ly + 16) 8 (ly_bot ly)).
{ replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn [aeval]; lia).
replace (ly_bot ly) with (aeval B ly (ATop (- kStackSpan))) by (cbn [aeval]; unfold ly_bot; lia).
apply (tfib_const_lookup_sym B TB ly S Hd mem (AT 16) 8 (ATop (- kStackSpan)) (proj1 HAR)). vm_compute. reflexivity. }
assert (V10 : val_mem tfibsegs m0 (ly_T ly + t_unwinding) 1 0).
{ replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
apply (cell_holds_val_mem B ly Hd mem (AT t_unwinding) 1 (ANum 0)).
apply (proj1 (Forall_forall _ _) (am_cells B ly S _ (proj1 HAR))).
unfold acells. do 8 (apply in_or_app; right). left. reflexivity. }
assert (P10 : apresent Hd mem (ly_T ly + t_unwinding)).
{ assert (TZ : zone3 (ly_T ly) kThreadObjSize).
{ pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD. destruct HD as (_ & _ & D3 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3))))))) as X.
exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) (RtDMallocUnw.T_high ly LY) X). }
eapply mbyte_off_apresent; [exact (zone3_off_img (ly_T ly) kThreadObjSize (ly_T ly + t_unwinding) TZ ltac:(unfold t_unwinding, kThreadObjSize; lia))|].
rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (V10 0%nat ltac:(lia)). }
(* ---- the entry state at 0x4cd64 ---- *)
set (EE := AE2y.Env regs []).
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0 - 2144) by (rewrite (EEr 2%nat 2%bv eq_refl); exact Hspz).
assert (PIN8 : getr regs 8%bv = sv_denot EE (SOff 2 2144)) by (cbn [sv_denot]; rewrite EE2, G8; unfold w64; f_equal; lia).
assert (PIN22 : getr regs 22%bv = sv_denot EE (SOff 2 0)) by (cbn [sv_denot]; rewrite EE2, G22; unfold w64; f_equal; lia).
assert (PIN23 : getr regs 23%bv = sv_denot EE (SOff 2 16)) by (cbn [sv_denot]; rewrite EE2, G23; unfold w64; f_equal; lia).
assert (HS0 : st_ok tfibsegs EE P2_SS0 (restrict Hd (mkst regs (Z_to_bv 64 0x4cd64) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold P2_SS0. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- unfold p2_regs.
apply (regs_ok_pin EE _ regs 23%bv (SOff 2 16)); [| intros X; discriminate X | exact PIN23].
apply (regs_ok_pin EE _ regs 22%bv (SOff 2 0)); [| intros X; discriminate X | exact PIN22].
apply (regs_ok_pin EE _ regs 8%bv (SOff 2 2144)); [| intros X; discriminate X | exact PIN8].
unfold EE, AE2y.Env. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB sd_rodata ly S Hd mem EE (sd_rodata_chk ly) (proj1 HAR))].
unfold region_ok, p2_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EE2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply AF0x.apresent_writable; [unfold TFIB_IMG_END; lia|]. apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold p2_stk, sd_rodata, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. unfold p2_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16.
repeat split; first [exact I | lia | replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia; rewrite Z_mod_plus_full; exact Hal]. }
(* ---- 0x4cd64 to the call of the unwinder ---- *)
unfold cfg_at, w64.
eapply SRr_bind; [exact (sd_phase_to W EE 0x603d8 P2_SS0 P2_U RS_running (mkst regs (Z_to_bv 64 0x4cd64) mem (seg_rom tfibsegs)) md HS0 p2_run_u)|].
cbv beta. intros W1 c1 _ (-> & msU & matU & -> & HSU & HFU & _).
change (st_ok tfibsegs EE P2_U (restrict Hd msU)) in HSU.
set (mdE := with_vm_backing (m_vm_lazy md) matU md) in *.
assert (SBME : same_but_materialized md mdE) by exact (with_vm_backing_same md matU). clearbody mdE.
cbn [ms_mem mkst] in HFU.
assert (MEQU : forall x : word, ~ (sp0 - 2144 <= bv_unsigned x < sp0 - 80) -> ms_mem msU x = mem x).
{ intros x Hx. apply HFU. intros Hin. apply Hx.
pose proof (in_wrange_single_b EE (ss_mem P2_SS0) (bv_unsigned x) 2 0 2064 (sp0 - 2144) p2_win0 EE2 Hin). lia. }
clear HFU.
pose proof p2_u_shape as (UPC & URV & UR1 & UR2 & UR4 & UR10 & UR11 & UR12 & UR13 & UR14 & UR15).
pose proof (st_ok_restrict_mkst tfibsegs Hd EE P2_U msU HSU URV) as UShape. rewrite UPC in UShape.
assert (SPU : bv_unsigned (getr (ms_regs msU) 2%bv) = sp0 - 2144).
{ rewrite (p2_reg_off Hd EE P2_U msU 2%bv 2 0 HSU UR2), EE2, Z.add_0_r. apply unsigned_lit_small. lia. }
assert (PRW : forall a, sp0 - 2144 <= a < sp0 - 80 -> apresent Hd (ms_mem msU) a).
{ intros a Ha. pose proof p2_u_r0_shape as (B0 & WL0 & WH0 & _).
apply (AF0x.st_ok_window_apresent Hd EE P2_U msU 0 p2_u_r0 a HSU p2_u_mem0); [| unfold TFIB_IMG_END; lia].
rewrite B0, WL0, WH0. cbn [base_val]. rewrite EE2. lia. }
assert (PRU : forall a, sp0 - 16384 <= a < sp0 -> apresent Hd (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [L|L]; [|destruct (Z_lt_le_dec a (sp0 - 80)) as [L2|L2]].
- apply (apresent_same Hd mem (ms_mem msU) a); [apply MEQU; rewrite unsigned_lit_small by lia; lia | apply Hpres; lia].
- apply PRW; lia.
- apply (apresent_same Hd mem (ms_mem msU) a); [apply MEQU; rewrite unsigned_lit_small by lia; lia | apply Hpres; lia]. }
assert (OUT : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= sp0 - 2144 \/ sp0 - 80 <= a) ->
val_mem tfibsegs m0 a k v -> val_mem tfibsegs (mrestrict Hd (ms_mem msU)) a k v).
{ intros a k v Ha Hk Ho Hv. exact (dm_val_mem_out Hd mem (ms_mem msU) (sp0 - 2144) (sp0 - 80) a k v MEQU Ha Hk Ho Hv). }
(* ---- the unwinder's premises ---- *)
assert (U10 : getr (ms_regs msU) 10%bv = Z_to_bv 64 (sp0 - 2144)).
{ rewrite (p2_reg_off Hd EE P2_U msU 10%bv 2 0 HSU UR10), EE2. f_equal. lia. }
assert (U11 : getr (ms_regs msU) 11%bv = Z_to_bv 64 PC_STRDUP_RA0) by exact (p2_reg_lit Hd EE P2_U msU 11%bv 0x4cdd0 HSU UR11).
assert (U12 : getr (ms_regs msU) 12%bv = Z_to_bv 64 sp0).
{ rewrite (p2_reg_off Hd EE P2_U msU 12%bv 2 2144 HSU UR12), EE2. f_equal. lia. }
assert (U13 : getr (ms_regs msU) 13%bv = Z_to_bv 64 0) by exact (p2_reg_lit Hd EE P2_U msU 13%bv 0 HSU UR13).
assert (U14 : getr (ms_regs msU) 14%bv = Z_to_bv 64 1) by exact (p2_reg_lit Hd EE P2_U msU 14%bv 1 HSU UR14).
assert (U15 : getr (ms_regs msU) 15%bv = Z_to_bv 64 30) by exact (p2_reg_lit Hd EE P2_U msU 15%bv 30 HSU UR15).
assert (U4 : getr (ms_regs msU) 4%bv = Z_to_bv 64 TFIB_TP).
{ rewrite (p2_reg_atom Hd EE P2_U msU 4%bv 4 HSU UR4), (EEr 4%nat 4%bv eq_refl), G4, (ts_tp B TB). reflexivity. }
assert (U1 : YK0s.ret_ok (getr (ms_regs msU) 1%bv)).
{ rewrite (p2_reg_lit Hd EE P2_U msU 1%bv 0x4ce8c HSU UR1). apply ret_ok_lit; [lia | reflexivity]. }
assert (UPC0 : 0 <= PC_STRDUP_RA0 < 2 ^ 64) by (unfold PC_STRDUP_RA0; lia).
assert (W1' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) 0xb1d98 1 1) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V1]).
assert (W2' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) 0xb0920 1 1) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V2]).
assert (W3' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) 0xb0924 4 0) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V3]).
assert (W4' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (TFIB_TP - 88) 8 TFIB_TSD)
by (apply OUT; [unfold TFIB_TP; lia | cbn; unfold TFIB_TP; lia | cbn; unfold TFIB_TP; lia | exact V4]).
assert (W5' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) TFIB_TSD 8 (ly_C ly))
by (apply OUT; [unfold TFIB_TSD; lia | cbn; unfold TFIB_TSD; lia | cbn; unfold TFIB_TSD; lia | exact V5]).
assert (W6' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (ly_C ly + 152) 8 (ly_T ly)) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V6]).
assert (W7' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (ly_T ly + 40) 1 0) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V7]).
assert (W8' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (ly_T ly + 8) 8 (ly_top ly)) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V8]).
assert (W9' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (ly_T ly + 16) 8 (ly_bot ly)) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V9]).
assert (W10' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (ly_T ly + t_unwinding) 1 0)
by (apply OUT; [unfold t_unwinding; lia | cbn; unfold t_unwinding; lia | cbn; unfold t_unwinding; lia | exact V10]).
assert (P10' : apresent Hd (ms_mem msU) (ly_T ly + t_unwinding)).
{ apply (apresent_same Hd mem (ms_mem msU)); [| exact P10]. apply MEQU. rewrite unsigned_lit_small by (unfold t_unwinding; lia). unfold t_unwinding. lia. }
assert (W11' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) 0xa63d0 8 0x140b60) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V11]).
assert (W12' : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) 0x140b60 8 4096) by (apply OUT; [lia | cbn; lia | cbn; lia | exact V12]).
assert (U16 : bv_unsigned (getr (ms_regs msU) 2%bv) mod 16 = 0).
{ rewrite SPU. replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
assert (Ulo : ly_stk_lo ly <= bv_unsigned (getr (ms_regs msU) 2%bv) - UNW_STK) by (rewrite SPU; unfold UNW_STK; lia).
assert (Upres : forall a, bv_unsigned (getr (ms_regs msU) 2%bv) - UNW_STK <= a < bv_unsigned (getr (ms_regs msU) 2%bv) ->
apresent Hd (ms_mem msU) a) by (intros a Ha; rewrite SPU in Ha; unfold UNW_STK in Ha; apply PRU; lia).
assert (Uth8 : (sp0 - 2144) mod 8 = 0) by (replace (sp0 - 2144) with (sp0 + (-268) * 8) by lia; rewrite Z_mod_plus_full; exact Hal8).
assert (Uthlo : ly_stk_lo ly <= sp0 - 2144) by lia.
assert (Uthsp : sp0 - 2144 + BST_SIZE <= bv_unsigned (getr (ms_regs msU) 2%bv) - UNW_STK \/ bv_unsigned (getr (ms_regs msU) 2%bv) <= sp0 - 2144)
by (right; rewrite SPU; lia).
assert (Uthp : forall a, sp0 - 2144 <= a < sp0 - 2144 + BST_SIZE -> apresent Hd (ms_mem msU) a)
by (intros a Ha; unfold BST_SIZE in Ha; apply PRW; lia).
assert (Uthbp : sp0 - 2144 + BST_SIZE <= sp0 - 16) by (unfold BST_SIZE; lia).
assert (Uspbp : bv_unsigned (getr (ms_regs msU) 2%bv) <= sp0 - 16) by (rewrite SPU; lia).
assert (Ura : rdword (aview tfibsegs Hd (ms_mem msU)) (sp0 - 8) = Some ra0).
{ eapply AF0x.rdword_ext; [|exact Hra0]. intros i Hi. apply aview_same. apply MEQU. rewrite unsigned_lit_small by lia. lia. }
assert (Unfp : rdword (aview tfibsegs Hd (ms_mem msU)) (sp0 - 16) = Some nfp0).
{ eapply AF0x.rdword_ext; [|exact Hnfp0]. intros i Hi. apply aview_same. apply MEQU. rewrite unsigned_lit_small by lia. lia. }
assert (Uch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) nfp0 then ch = []
else sp0 + 16 <= nfp0 /\ fpchain (rdword (aview tfibsegs Hd (ms_mem msU))) nfp0 (ly_top ly) ch)
else ch = []).
{ pose proof Hch as Hch'. destruct (sp0 + 16 <? ly_top ly); [|exact Hch'].
destruct (bad_next sp0 (ly_top ly) nfp0) eqn:Hb; [exact Hch'|].
destruct Hch' as [H16 Hfp]. split; [exact H16|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb2.
eapply AF0x.fpchain_ext2; [exact Hfp | lia |].
intros a va Ha1 Ha2 Hva. eapply AF0x.rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply MEQU. rewrite unsigned_lit_small by lia. lia. }
(* ---- the unwinder ---- *)
pose proof (UNWIND W ly (ms_regs msU) (ms_mem msU) mdE (sp0 - 2144) PC_STRDUP_RA0 sp0 ra0 nfp0 ch LY IMG
U10 U11 U12 U13 U14 U15 U4 U1 UPC0 W1' W2' W3' W4' W5' W6' W7' W8' W9' W10' P10' W11' W12'
U16 Ulo Upres Uth8 Uthlo Uthsp Uthp Uthbp Uspbp Hbot Hshi Hal8 Ura Unfp Hra4096 Uch) as UW.
rewrite UShape. eapply SRr_bind; [exact UW|]. clear UW.
intros W2 c2 _ (-> & regs' & mem' & mat' & -> & URP & UFR & UPR & USZ & UFRM & UTOP).
rewrite (p2_reg_lit Hd EE P2_U msU 1%bv 0x4ce8c HSU UR1).
set (mdU := with_vm_backing (m_vm_lazy mdE) mat' mdE) in *.
assert (SBMU : same_but_materialized md mdU) by exact (same_but_materialized_trans md mdE mdU SBME (with_vm_backing_same mdE mat')).
clearbody mdU.
assert (MEQ' : forall z : word, ~ (sp0 - 2288 <= bv_unsigned z < sp0 - 80) -> mem' z = ms_mem msU z).
{ intros z Hz. apply UFR; rewrite ?SPU; unfold UNW_STK, BST_SIZE; lia. }
(* ---- after the unwinder: no region is kept, the next three instructions touch no memory ---- *)
pose proof (st_ok_after_call tfibsegs P2_HAV EE P2_U (restrict Hd msU) regs' (mrestrict Hd mem') [] 0x4ce8c HSU URV
(proj1 p2_u_atoms) (proj1 (proj2 p2_u_atoms)) (proj1 (proj2 (proj2 p2_u_atoms))) (proj2 (proj2 (proj2 p2_u_atoms)))
p2_submem UR1 URP (Forall_nil _)) as HS1.
rewrite p2_1_eq in HS1. rewrite <- (restrict_mkst_fx Hd) in HS1.
set (E1 := havoc EE P2_HAV (map (getr regs') CLOB)) in *.
assert (E1o : forall k, (k < 64)%nat -> ew E1 k = ew EE k) by (intros k Hk; exact (ew_havoc_old EE P2_HAV (map (getr regs') CLOB) k Hk)).
assert (E12 : bv_unsigned (ew E1 2) = sp0 - 2144) by (rewrite (E1o 2%nat ltac:(lia)); exact EE2).
(* ---- 0x4ce8c to the call of asan_malloc ---- *)
eapply SRr_bind; [exact (sd_phase_to W E1 0x34528 P2_1 P2_A RS_running (mkst regs' (Z_to_bv 64 0x4ce8c) mem' (seg_rom tfibsegs)) mdU HS1 p2_run_a)|].
cbv beta. intros W3 c3 _ (-> & ms2 & mat2 & -> & HSA & HFA & _).
change (st_ok tfibsegs E1 P2_A (restrict Hd ms2)) in HSA.
set (md2 := with_vm_backing (m_vm_lazy mdU) mat2 mdU) in *.
assert (SBM2 : same_but_materialized md md2) by exact (same_but_materialized_trans md mdU md2 SBMU (with_vm_backing_same mdU mat2)).
clearbody md2.
cbn [ms_mem mkst] in HFA.
assert (MEQA : forall z, ms_mem ms2 z = mem' z).
{ intros z. apply HFA. intros (r & Hr & _). rewrite p2_1_mem in Hr. destruct Hr. }
clear HFA.
pose proof p2_a_shape as (APC & ARV & AR1 & AR2 & AR3 & AR4 & AR8 & AR9 & AR10 & AR11 & AR18 & AR22 & AR23 & AR24 & AR25 & AR26 & AR27).
pose proof (st_ok_restrict_mkst tfibsegs Hd E1 P2_A ms2 HSA ARV) as AShape. rewrite APC in AShape.
(* the memory at the call against the one at 0x4cd64 *)
assert (MEQ_all : forall z : word, ~ (sp0 - 2288 <= bv_unsigned z < sp0 - 80) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite MEQA, MEQ' by exact Hz. apply MEQU. intros X. apply Hz. lia. }
assert (AV_all : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2288 <= a < sp0 - 80) -> aview tfibsegs Hd (ms_mem ms2) a = aview tfibsegs Hd mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ_all. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PR_all : forall a, apresent Hd mem a -> apresent Hd (ms_mem ms2) a).
{ intros a Hp. apply (apresent_same Hd mem' (ms_mem ms2) a (MEQA _)). apply UPR.
rewrite (AE2y.apresent_mod _ (ms_mem msU) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1];
[apply (apresent_same Hd mem (ms_mem msU) a'); [apply MEQU; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' (sp0 - 80)) as [L2|L2]; [apply PRW; lia|].
apply (apresent_same Hd mem (ms_mem msU) a'); [apply MEQU; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms2) md2).
{ destruct (same_but_materialized_frame md md2 SBM2) as (_ & V1m & V2m & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3m).
apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms2) md2 HAR).
- intros a Ha Ho. apply AV_all; [exact Ha|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Ho).
- intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms2) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2288)) as [L1|L1]; [rewrite AV_all by lia; exact Hv|].
destruct (Z_lt_le_dec a' (sp0 - 80)) as [L3|L3]; [| rewrite AV_all by lia; exact Hv].
apply aview_some_of_apresent. apply PR_all. apply Hpres. lia.
- exact V1m.
- exact V2m.
- exact V3m.
- exact (AE2y.hs_kept_win Hd mem mem (ms_mem ms2) (sp0 - 2288) (sp0 - 80) (sp0 - 16384) sp0 MEQ_all Hpres ltac:(lia) ltac:(lia)). }
(* the trace object at sp0 - 2144 *)
assert (TRB : forall x, In x (sd_trace ly sp0 ra0 nfp0 ch) -> 0 <= x < 2 ^ 64).
{ apply p2_trace_bound; [exact (dm_rdword_range _ _ _ _ Hra0)|].
pose proof Hch as Hch'. destruct (sp0 + 16 <? ly_top ly); [|rewrite Hch'; constructor].
destruct (bad_next sp0 (ly_top ly) nfp0); [rewrite Hch'; constructor|].
exact (dm_fpchain_bound Hd mem _ _ ch (proj2 Hch')). }
assert (OBJ0 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2144) 8 (sp0 - 2128)).
{ pose proof p2_u_r0_shape as (B0 & _ & _ & _ & K2).
pose proof (AF0x.st_ok_chunk_val Hd EE P2_U msU 0 p2_u_r0 2 _ _ _ (sp0 - 2128) HSU p2_u_mem0 K2) as X.
rewrite B0 in X. cbn [base_val] in X. rewrite EE2, Z.add_0_r in X.
apply X; [cbn [sv_denot]; rewrite EE2; f_equal; lia | cbn; lia | cbn; lia]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2136) 8 0).
{ pose proof p2_u_r0_shape as (B0 & _ & _ & K1 & _).
pose proof (AF0x.st_ok_chunk_val Hd EE P2_U msU 0 p2_u_r0 1 _ _ _ 0 HSU p2_u_mem0 K1) as X.
rewrite B0 in X. cbn [base_val] in X. rewrite EE2 in X. replace (sp0 - 2144 + 8) with (sp0 - 2136) in X by lia.
apply X; [reflexivity | cbn; lia | cbn; lia]. }
assert (UKEEP : forall a k v, sp0 - 2144 <= a -> (a + Z.of_nat k <= sp0 - 2136 \/ (sp0 - 2132 <= a /\ a + Z.of_nat k <= sp0 - 2128)) ->
val_mem tfibsegs (mrestrict Hd (ms_mem msU)) a k v -> val_mem tfibsegs (mrestrict Hd (ms_mem ms2)) a k v).
{ intros a k v Ha Hk Hv. apply (val_mem_frame Hd (ms_mem msU) (ms_mem ms2) a k v); [|exact Hv].
intros j Hj. rewrite MEQA. apply UFR; rewrite ?SPU; rewrite unsigned_lit_small by lia; unfold UNW_STK, BST_SIZE; lia. }
assert (ATR : astrace_at tfibsegs W (ms_mem ms2) (sp0 - 2144) (sd_trace ly sp0 ra0 nfp0 ch)).
{ split; [|split; [|split]].
- apply val_mem_rdword; [lia|]. replace (sp0 - 2144 + 16) with (sp0 - 2128) by lia.
apply UKEEP; [lia | cbn; lia | exact OBJ0].
- apply dm_rd32_of_val_mem. eapply val_mem_frame; [|exact USZ]. intros j Hj. apply MEQA.
- apply dm_rd32_of_val_mem.
assert (Z4 : val_mem tfibsegs (mrestrict Hd (ms_mem msU)) (sp0 - 2144 + 12) 4 0).
{ intros k Hk. replace (sp0 - 2144 + 12 + Z.of_nat k) with (sp0 - 2136 + Z.of_nat (4 + k)) by lia.
rewrite (OBJ1 (4 + k)%nat ltac:(lia)).
assert (LB0 : forall w j, le_byte 0 w j = 0).
{ intros w j. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
rewrite !LB0. reflexivity. }
apply UKEEP; [lia | cbn; lia | exact Z4].
- intros i Hi. apply val_mem_rdword; [apply TRB; apply nth_In; exact Hi|].
eapply val_mem_frame; [|exact (UFRM i Hi)]. intros j Hj. apply MEQA. }
(* ---- the post ---- *)
apply SRr_ret. unfold sd_p2_post. split; [reflexivity|].
exists (ms_regs ms2), (ms_mem ms2), md2.
split; [unfold cfg_at; f_equal; exact AShape|].
split; [exact HAR2|]. split; [exact SBM2|].
split; [exact (p2_reg_lit Hd E1 P2_A ms2 1%bv 0x4ce9c HSA AR1)|].
split; [rewrite (p2_reg_off Hd E1 P2_A ms2 2%bv 2 0 HSA AR2), E12; unfold w64; f_equal; lia|].
split; [rewrite (p2_reg_atom Hd E1 P2_A ms2 10%bv 18 HSA AR10), (E1o 18%nat ltac:(lia)), (EEr 18%nat 18%bv eq_refl); exact G18|].
split; [rewrite (p2_reg_off Hd E1 P2_A ms2 11%bv 2 0 HSA AR11), E12; unfold w64; f_equal; lia|].
split; [rewrite (p2_reg_atom Hd E1 P2_A ms2 3%bv 3 HSA AR3), (E1o 3%nat ltac:(lia)); exact (EEr 3%nat 3%bv eq_refl)|].
split; [rewrite (p2_reg_atom Hd E1 P2_A ms2 4%bv 4 HSA AR4), (E1o 4%nat ltac:(lia)); exact (EEr 4%nat 4%bv eq_refl)|].
split; [rewrite (p2_reg_off Hd E1 P2_A ms2 8%bv 2 2144 HSA AR8), E12, G8; unfold w64; f_equal; lia|].
split; [rewrite (p2_reg_atom Hd E1 P2_A ms2 9%bv 9 HSA AR9), (E1o 9%nat ltac:(lia)); exact (EEr 9%nat 9%bv eq_refl)|].
split; [rewrite (p2_reg_atom Hd E1 P2_A ms2 18%bv 18 HSA AR18), (E1o 18%nat ltac:(lia)); exact (EEr 18%nat 18%bv eq_refl)|].
split.
{ intros r Hr.
assert (Er : r = Z_to_bv 5 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hc : bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E in Er; subst r.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_off Hd E1 P2_A ms2 22%bv 2 0 HSA AR22), E12, G22. unfold w64. f_equal. lia.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_off Hd E1 P2_A ms2 23%bv 2 16 HSA AR23), E12, G23. unfold w64. f_equal. lia.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_atom Hd E1 P2_A ms2 24%bv 24 HSA AR24), (E1o 24%nat ltac:(lia)). exact (EEr 24%nat 24%bv eq_refl).
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_atom Hd E1 P2_A ms2 25%bv 25 HSA AR25), (E1o 25%nat ltac:(lia)). exact (EEr 25%nat 25%bv eq_refl).
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_atom Hd E1 P2_A ms2 26%bv 26 HSA AR26), (E1o 26%nat ltac:(lia)). exact (EEr 26%nat 26%bv eq_refl).
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (p2_reg_atom Hd E1 P2_A ms2 27%bv 27 HSA AR27), (E1o 27%nat ltac:(lia)). exact (EEr 27%nat 27%bv eq_refl). }
split; [exact ATR|].
split.
- intros a Ha Hout. apply AV_all; [exact Ha|]. intros X. apply Hout. lia.
- exact PR_all.
Qed.

End p2.
