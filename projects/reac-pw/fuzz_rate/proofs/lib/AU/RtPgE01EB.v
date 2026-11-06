(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88 (the register readers rx_reg_atom / rx_reg_lit and the tactics rx_atom / rx_lit, kept as e01e_reg_atom / e01e_reg_lit / e01e_atom / e01e_lit), proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxEntry.v at 09c6822d8861 (eb_land_m32 and eb_denot_and_m32, kept as e01e_land_m32 and e01e_denot_and_m32; the plan of gb_entry_a) and proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxFrame.v at 09c6822d8861 (val_mem_of_rd32, kept as e01e_val_mem_rd32) [Apache-2.0 OR MIT, used under Apache-2.0]; module paths changed to reac_pw.fuzz_rate, the walk of part ENT of reac-pw/fuzz_rate's segment S_E01 below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01E.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's code of part ENT (the frame 0x220, the GOT words 0x9c1c8 / 0x9c170 and their
   cells 0xa4f40 / 0xa4f38, s2 = p, s4 = the shadow offset), the class-4 call __asan_stack_malloc_4 (its flag pointer
   word at F + 0x3f8), the harness records of lib/AU (rhb_ / rsb_ / rtsb_ names), the names e01e_ renamed e01eb_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): PART ENT of segment S_E01 of
   the walk of LLVMFuzzerTestOneInput (0x8076c), from ENTRY 0x8076c to FR 0x807e0 (__asan_stack_malloc_4 returned).
   Proves lib/AU/RtPgE01DB.v e01b_ent_stmt (kind: segment lemma, one part of S_E01). Proves no function.

   THE CODE (29 words 0x8076c .. 0x807dc, all 4-byte encodings):
     0x8076c addi sp,sp,-0x220          0x80770 sd zero,0(sp)                    (S - 0x220, S the entry sp)
     0x80774 sd ra,0x218(sp) .. 0x807a4 sd s11,0x1b8(sp)   the 13 saves at S - 8 .. S - 0x68 (RtPgSegB.rsb_saved_regs)
     0x807a8 addi s0,sp,0x220 (s0 = S)  0x807ac andi sp,sp,-0x20       0x807b0 mv s1,sp   (sp = s1 = R)
     0x807b4 mv s5,a1 (n)               0x807b8 auipc a1 / 0x807bc auipc a2
     0x807c0 ld a2 <- 0x9c1c8 (the GOT word of the use-after-return option: 0xa4f40)
     0x807c4 ld a1 <- 0x9c170 (the GOT word of the shadow-offset cell: 0xa4f38)
     0x807c8 lw a2,0(a2) (the option, 1)     0x807cc ld s4,0(a1) (SHADOW_OFF)      0x807d0 mv s2,a0 (p)
     0x807d4 beqz a2 -> 0x807e8: NOT taken (a2 = 1), so 0x807e8 (s8 = 0) and the real-stack arm 0x807f4 .. 0x8080c
       are never walked
     0x807d8 addi a0,zero,0x2c0         0x807dc jal 0x3d300 (__asan_stack_malloc_4, ra = 0x807e0)
   with R = 32 * ((S - 0x220) / 32), so R - S is -0x220 or -0x230.

   THE PROOF. (1) The harness journal from the entry (YCbq.ajournal_init on rhb_base's afn_pre: sp0 = S, FP = [],
   own = [], no event). (2) The entry symbolic state over Ereg (entry registers) []: one stack region at atom 2
   (sp) over [S - 0x220, S), writable (the journal's window [S - LLVMF_STK, S), HSTK), and four base-free read-only
   regions for the two GOT words, the shadow-offset cell and the option's four bytes, their values from AR's
   const law (YG0d.AR_const_law, at HGOT / HSC / HGOTU / HUAR). (3) One engine run (YCbq.aj_run) to 0x3d300; the
   run's last state gives sp = s1 = R (the `andi`), s0 = S, s2 = p, s4 = SHADOW_OFF, s5 = n, gp, tp, ra = 0x807e0 and
   the 13 saves as chunks of the stack region. (4) The call through YCbq.aj_stack_malloc_at (class 4,
   o = R - S): the journal gains own = [(4, pos)], the frame is the only frame, a0 = frame_addr (entry layout) 4 pos,
   the flag pointer word sits at F + 0x3f8 = F + 1024 - 8, and acall_kept keeps every byte above alloc_ceiling
   outside [R - ESTACK, R), so the saves survive. (5) The FR state e01b_fr: the input bytes at p by the final
   journal's entry-block clause (FP = []), the registers by aregs_preserved, and the continuation e01b_from_fr. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgE01DB RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the code and the entry symbolic state ======================================== *)
Definition E01EB_NW : nat := 29.
Definition e01eb_tbl : ctable := build_table rsegs RSB_ENTRY E01EB_NW TEmpty.
Lemma e01eb_tbl_ok : table_ok rsegs e01eb_tbl.
Proof. apply build_table_ok0. unfold RSB_ENTRY. lia. Qed.
(* the machine stack below the entry sp (atom 2): `sd zero,0(sp)` at S - 0x220 and the 13 saves at S - 0x68 .. S *)
Definition e01eb_rstk : YP09.region := YP09.mkRegion (Some 2%nat) (-0x220) 0 (-0x220) 0 [].
(* the GOT word of the use-after-return option (0x9c1c8 -> 0xa4f40), the GOT word of the shadow-offset cell
   (0x9c170 -> 0xa4f38), the shadow-offset cell (SHADOW_OFF) and the option's four bytes (1) *)
Definition e01eb_rgu : YP09.region := YP09.mkRegion None 0x9c1c8 0x9c1d0 0 0 [YP09.mkChunk 0x9c1c8 (CVal 8 (SLit 0xa4f40))].
Definition e01eb_rgs : YP09.region := YP09.mkRegion None 0x9c170 0x9c178 0 0 [YP09.mkChunk 0x9c170 (CVal 8 (SLit 0xa4f38))].
Definition e01eb_rcs : YP09.region := YP09.mkRegion None 0xa4f38 0xa4f40 0 0 [YP09.mkChunk 0xa4f38 (CVal 8 (SLit SHADOW_OFF))].
Definition e01eb_rcu : YP09.region := YP09.mkRegion None 0xa4f40 0xa4f44 0 0 [YP09.mkChunk 0xa4f40 (CVal 4 (SLit 1))].
Definition e01eb_ss0 : sstate :=
  mkSS RSB_ENTRY sr_atoms [e01eb_rstk; e01eb_rgu; e01eb_rgs; e01eb_rcs; e01eb_rcu] None (mkFacts [] [] []).
(* the engine's sp after `andi sp,sp,-0x20`, and s1 after `mv s1,sp` (measured: sym_runN stops at 0x3d300 with
   RS_stopped SR_fetch) *)
Definition E01EB_SPR : sv := SAlu ALU_AND (SOff 2 (-544)) (SLit (-32)).
Definition E01EB_S1R : sv := SAlu ALU_ADD E01EB_SPR (SLit 0).

(* ======================================== generic lemmas ======================================== *)
Lemma e01eb_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma e01eb_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite e01eb_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma e01eb_denot_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), (denot_lit_U E x). f_equal.
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* four bytes read as rd32, as a val_mem *)
Lemma e01eb_val_mem_rd32 : forall segs H mem a v,
rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* a base-free read-only region holding one literal cell *)
Lemma e01eb_ro_cell : forall E (H : word -> bool) mem a hi (n : N) v,
hi = a + Z.of_N n -> 0 <= a -> hi <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem rsegs (mrestrict H mem) a (N.to_nat n) v ->
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion None a hi 0 0 [YP09.mkChunk a (CVal n (SLit v))]).
Proof.
intros E H mem a hi n v Ehi Ha Hhi Hv Hn Hm. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val rsegs E _ 0 a n (SLit v) v); [reflexivity | exact Hv | exact Hn | rewrite Z.add_0_l; exact Hm].
Qed.
(* a register of a run's last state, read off the symbolic state *)
Lemma e01eb_reg_sv : forall segs E ss ms (H : word -> bool) (r : bv 5) e,
st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros segs E ss ms H r e HS He. rewrite (st_ok_restrict_reg segs H E ss ms r HS), He. reflexivity. Qed.
Lemma e01eb_reg_atom : forall segs ss ms (H : word -> bool) regs extra (r r' : bv 5) (n : nat),
st_ok segs (Ereg regs extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros segs ss ms H regs extra r r' n HS Hg Hn. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
Lemma e01eb_reg_lit : forall segs E ss ms (H : word -> bool) (r : bv 5) z,
st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros segs E ss ms H r z HS Hg. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hg. reflexivity. Qed.
(* the realigned base R of the real frame, as the engine's sv *)
Lemma e01eb_den_R : forall regs extra, 544 <= spZ regs ->
sv_denot (Ereg regs extra) E01EB_SPR = Z_to_bv 64 (32 * ((spZ regs - 0x220) / 32)).
Proof.
intros regs extra H. assert (Hr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
replace (spZ regs - 0x220) with (spZ regs + -544) by lia. unfold E01EB_SPR.
apply e01eb_denot_and_m32; [|lia | lia | lia].
rewrite (ew_Ereg_nat regs extra 2 2%bv eq_refl). unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a save of the prologue, read off a chunk of the stack region (atom 2) *)
Lemma e01eb_save : forall segs m regs0 extra cs lo hi wlo whi j,
region_ok segs (Ereg regs0 extra) m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (bv_unsigned (nth j rsb_saved_regs 0%bv))) 0))) cs ->
val_mem segs m (spZ regs0 + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs0 (nth j rsb_saved_regs 0%bv))).
Proof.
intros segs m regs0 extra cs lo hi wlo whi j (_ & _ & _ & Hcs) Hin.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base base_val] in Hc.
rewrite (ew_Ereg_nat regs0 extra 2 2%bv eq_refl) in Hc.
change (bv_unsigned (getr regs0 2%bv)) with (spZ regs0) in Hc.
apply (val_of_chunk_ok segs _ m _ _ 8 _ _ Hc).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_Ereg_reg. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr regs0 (nth j rsb_saved_regs 0%bv))). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- lia.
Qed.
End a.

(* the value of a register after a run, from the symbolic state *)
Ltac e01eb_atom HS r r' H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (e01eb_reg_atom segs ss ms Hh rg ex r r' n HS); vm_compute; reflexivity) end end.
Ltac e01eb_lit HS r H :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SLit ?z =>
assert (H : getr (ms_regs ms) r = Z_to_bv 64 z)
  by (apply (e01eb_reg_lit segs E ss ms Hh r z HS); vm_compute; reflexivity) end end.
(* a callee-saved register index *)
Ltac e01eb_cs :=
lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z; unfold acallee_saved; lia end.

(* ======================================== the part ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HBsm4 : pc_stack_malloc (as_code B) 4 = E01B_SM4.
Hypothesis HGOT : as_got_shadow B = 0x9c170.
Hypothesis HSC : as_shadow_cell B = 0xa4f38.
Hypothesis HGOTU : as_got_uar B = 0x9c1c8.
Hypothesis HUAR : as_uar_cell B = 0xa4f40.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.

Theorem e01b_ent_ok : e01b_ent_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold e01b_ent_stmt. intros hx POST HB HK.
destruct hx as [ly A0 W regs mem md p n pl].
unfold rhb_base in HB. unfold e01b_from_fr in HK.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl] in HB |- *.
destruct HB as (HPRE & _ & Hp & Hn & Hpn & Hlen & Hpl & Hfr0 & _ & _ & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as HL.
assert (HJ : ajournal rsegs B LLVMF_STK (spZ regs) [] ly A0 W mem md [] ly A0 W mem md 0)
  by (eapply ajournal_init; exact HPRE).
pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & Hpres0 & _ & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_const _ _ HL _ _ _ _ _ HAR0) as (Kcell & Kuar & Kgot & Kguar).
rewrite HSC in Kcell. rewrite HUAR in Kuar. rewrite HGOT, HSC in Kgot. rewrite HGOTU, HUAR in Kguar.
set (S0 := spZ regs) in *.
remember (32 * ((S0 - 0x220) / 32)) as R eqn:ER.
assert (HR : R mod 16 = 0 /\ S0 - 0x230 <= R <= S0 - 0x220).
{ rewrite ER.
  pose proof (Z.div_mod (S0 - 544) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S0 - 544) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod S0 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  set (q := (S0 - 544) / 32) in *. set (rr := (S0 - 544) mod 32) in *. set (u := S0 / 16) in *.
  split; [replace (32 * q) with ((2 * q) * 16) by lia; apply Z_mod_mult | lia]. }
destruct HR as (HR16 & HRlo & HRhi).
assert (Ho16 : (R - S0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hal16; reflexivity).
assert (Bsp : bv_unsigned (ew (Ereg regs []) 2) = S0) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
(* ---- the entry symbolic state ---- *)
assert (HS : st_ok rsegs (Ereg regs []) e01eb_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RSB_ENTRY) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold e01eb_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold e01eb_rstk, e01eb_rgu, e01eb_rgs, e01eb_rcs, e01eb_rcu.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + apply (region_ok_stack rsegs _ _ 2 S0 (-0x220) Bsp); [lia | lia |].
      intros a Ha. apply (apresent_writable rsegs). apply Hpres0. lia.
    + apply (e01eb_ro_cell _ _ _ 0x9c1c8 0x9c1d0 8 0xa4f40); [reflexivity | lia | lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kguar).
    + apply (e01eb_ro_cell _ _ _ 0x9c170 0x9c178 8 0xa4f38); [reflexivity | lia | lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kgot).
    + apply (e01eb_ro_cell _ _ _ 0xa4f38 0xa4f40 8 SHADOW_OFF); [reflexivity | lia | lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | lia |].
      exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kcell).
    + apply (e01eb_ro_cell _ _ _ 0xa4f40 0xa4f44 4 1); [reflexivity | lia | lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
      exact (e01eb_val_mem_rd32 rsegs (w_H W) mem _ _ Kuar).
  - unfold e01eb_rstk, e01eb_rgu, e01eb_rgs, e01eb_rcs, e01eb_rcu. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Bsp. repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
(* ---- the run 0x8076c .. the jal of __asan_stack_malloc_4 ---- *)
unfold cfg_at. change (w64 RSB_ENTRY) with (Z_to_bv 64 RSB_ENTRY).
aj_run e01eb_tbl_ok HS HJ.
{ unfold e01eb_ss0, e01eb_rstk, e01eb_rgu, e01eb_rgs, e01eb_rcs, e01eb_rcu. cbn [ss_mem].
  eapply (awr_ok_cons_stack _ _ _ _ _ _ _ _ _ _ 2%nat); [reflexivity | exact Bsp | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the run's last state *)
assert (Q2 : getr (ms_regs ms) 2%bv = Z_to_bv 64 R).
{ rewrite (e01eb_reg_sv rsegs _ _ _ _ 2%bv E01EB_SPR HS ltac:(vm_compute; reflexivity)).
  rewrite (e01eb_den_R regs [] ltac:(change (spZ regs) with S0; lia)). rewrite ER. reflexivity. }
assert (Q9 : getr (ms_regs ms) 9%bv = Z_to_bv 64 R).
{ rewrite (e01eb_reg_sv rsegs _ _ _ _ 9%bv E01EB_S1R HS ltac:(vm_compute; reflexivity)).
  unfold E01EB_S1R. rewrite e01eb_denot_add0.
  rewrite (e01eb_den_R regs [] ltac:(change (spZ regs) with S0; lia)). rewrite ER. reflexivity. }
e01eb_atom HS (8%bv : bv 5) (2%bv : bv 5) Q8.
e01eb_atom HS (3%bv : bv 5) (3%bv : bv 5) Q3.
e01eb_atom HS (4%bv : bv 5) (4%bv : bv 5) Q4.
e01eb_atom HS (18%bv : bv 5) (10%bv : bv 5) Q18.
e01eb_atom HS (21%bv : bv 5) (11%bv : bv 5) Q21.
e01eb_lit HS (20%bv : bv 5) Q20.
e01eb_lit HS (1%bv : bv 5) Q1.
(* the 13 saves, from the stack region *)
lazymatch type of HS with st_ok _ _ ?ssc _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssc) 0) in
  lazymatch r0 with Some ?rr =>
    pose proof (rtsb_region_nth _ ssc ms 0 rr (w_H W) HS ltac:(vm_compute; reflexivity)) as HR0 end end.
assert (HSV : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (S0 + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr regs (nth j rsb_saved_regs 0%bv)))).
{ intros j Hj. apply (e01eb_save rsegs _ regs [] _ _ _ _ _ j HR0).
  do 13 (destruct j as [|j]; [vm_compute; repeat (first [left; reflexivity | right]) |]). lia. }
clear HR0.
(* ---- __asan_stack_malloc_4(0x2c0) at 0x3d300, ra 0x807e0 ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1. cbn [ss_pc].
replace (Z_to_bv 64 250624) with (Z_to_bv 64 (pc_stack_malloc (as_code B) 4)) by (rewrite HBsm4; reflexivity).
eapply SRr_bind.
{ eapply (aj_stack_malloc_at rsegs B HL Hsegs HAPI ML SMP 4 ASM4 ltac:(lia)
    W (ms_regs ms) (ms_mem ms) LLVMF_STK S0 [] ly A0 W mem md [] ly A0 _ 0 (R - S0) (Z_to_bv 64 E01B_FR) HJ).
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - rewrite Hes. lia.
  - rewrite Q3. exact Hgp0.
  - rewrite Q4. exact Htp0.
  - exact Q1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & _ & _ & _ & _ & Hflag & HKc).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
pose proof HJ2 as (HAR2 & _).
assert (Hfin2 : In (4, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_flag _ _ HL _ _ _ _ _ 4 pos HAR2 Hfin2) as (_ & _ & HFLapp & HFLc).
unfold in_app in HFLapp.
destruct HKc as (HK1 & _).
(* ---- the FR state ---- *)
refine (HK pos ly S2 W regs2 mem2 md2 _).
unfold e01b_fr, e01b_base, rhb_j, rhb_kept, e01b_env, e01b_R, e01b_S, e01b_F.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl].
split; [split; [exact HJ2|]; split; [rewrite Hfrs2, Hfr0; reflexivity|]; split; [exact Eab|]; split|].
- (* the 13 saves and the flag pointer word *)
  unfold rhb_cells. apply Forall_app. split.
  + unfold rhb_saves_L. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
    cbn [fst snd rt_at rt_xv q_S].
    rewrite Z.mod_small by apply u64_range.
    apply (val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem2); [|apply HSV; lia].
    intros k Hk. change (spZ regs) with S0. apply HK1; lia.
  + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd rt_at rt_xv q_F]. unfold RSB_CID.
    change (fs_frame_bytes 4) with 1024 in Hflag.
    replace (frame_addr ly 4 pos + 0x3f8) with (frame_addr ly 4 pos + 1024 - 8) by lia.
    rewrite Z.mod_small by lia.
    exact (val_mem_of_rdword rsegs (w_H W) mem2 _ _ Hflag).
- (* the input bytes at p *)
  destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)].
  + destruct pl as [|b pl]; [cbn [map]; apply garr8_nil | cbn [length] in Hlen; lia].
  + intros j Hj. destruct (Hpl j Hj) as [Hv Hb]. split; [|exact Hb].
    rewrite length_map in Hj.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    assert (Hinp2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hinp).
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply (val_mem_kept rsegs (w_H W) (w_H W) mem mem2); [|exact Hv].
    intros k Hk. cbn [Z.of_nat] in Hk.
    replace (p + Z.of_nat j + k) with (p + (Z.of_nat j + k)) by lia.
    apply (F2 p n (Z.of_nat j + k) Hinp Hinp2); [lia | intros (rg & [] & _)].
- (* the registers *)
  split; [rewrite (KP 2%bv ltac:(e01eb_cs)), Q2, ER; reflexivity|].
  split; [rewrite (KP 3%bv ltac:(e01eb_cs)), Q3; exact Hgp0|].
  split; [rewrite (KP 4%bv ltac:(e01eb_cs)), Q4; exact Htp0|].
  split; [rewrite (KP 8%bv ltac:(e01eb_cs)), Q8; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite (KP 9%bv ltac:(e01eb_cs)), Q9, ER; reflexivity|].
  split; [rewrite (KP 18%bv ltac:(e01eb_cs)), Q18; exact Hp|].
  split; [rewrite (KP 20%bv ltac:(e01eb_cs)), Q20; reflexivity|].
  split; [rewrite (KP 21%bv ltac:(e01eb_cs)), Q21; exact Hn|].
  exact Ha0.
Qed.
End b.

About e01b_ent_ok.
Print Assumptions e01b_ent_ok.
