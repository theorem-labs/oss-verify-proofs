(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_next.v, the NEXT stage of the image-B (fuzz_reply.asan-ubsan) walk
   of fuzz_reply's drain.  Proves no function (kind: segment lemma): dr_next : dr_next_stmt B MT MMAX RG, the
   statement of lib/B/W_drain_cx.v (a working branch; that file is not edited).
   The walk, from fuzz_reply.asan-ubsan's objdump, from DLN 0x839d4 (s7 = buf + p - 1, the NUL that ended the line):
     0x839d4  addi s8,s7,1                    s8 = buf + p, the next line's start
     0x839d8  li s10,384                      the scan bound DLL / DLR carry
     0x839dc  li a0,-1
     0x839e0  bne s7,a0 -> 0x8395c            the UBSan pointer-overflow check of s7 + 1 (PTR_EQK_FT): its
     0x839e4  j 0x84004 (unimp)                NOT-TAKEN edge traps.  Refuted with the trap kit's recipe for this
                                              site (lib/B/W_traps.v census row "WRAP p+1 = 0, ft",
                                              a working branch 6c73ae99620): R1 (s7's atom fact 4096 .. DCEIL) plus
                                              the seated closer trap_seat (trap_br_eq ..) : acond_ok (s7 <> -1), so
                                              the runner decides the branch taken.
   then 0x8395c is lib/B/W_drain_join.v's cut DJ at p, and dr_memchr_join ends in DLL p q or DLR p.
   STRUCTURE PORTED FROM a working branch 1c09e330abe lib/B/Prog/drain_p_next_step.v (the step
   from the line's NUL to the next memchr); nothing is copied, the vocabulary is this framework's.
   ARx FORM (an internal work row): Section cx proves dr_next_x, W_drain_cx_x.v's dr_next_stmt_x, over any allocator relation ARx
   (the twin of lib/A/W_drain_next.v's dr_next_x of DR_x slice B): the same walk to DJ, then W_drain_join.v's
   dr_memchr_join_x; its journal is at W_contract_x.v's DRAIN_STK_x; the AR walk dr_next (Section c) is unchanged. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_dnrk W_drain_join W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
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

(* ------------------------------------------------------------------ the symbolic state at 0x839d4 *)
(* Atoms 0..31: the registers; 32 = SHADOW_OFF (no memory is read before 0x8395c, so no region and no shadow entry). *)
Definition dn_Bx : sv := SOff 32 0.
Definition dn_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition dn_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF 4096 140737479966720 0);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ]
          [ mkAC BC_NE (SOff 23 0) (SLit 18446744073709551615) ] [].
Definition dn_ss : sstate := mkSS A_dr_next sr_atoms [] None dn_facts.
Definition dn_extra : list word := [Z_to_bv 64 SHADOW_OFF].

Lemma dn_seat : forall (W1 : world SEGS) regs1 m1 sp y,
spZ regs1 = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 23 = w64 y -> 4096 <= y <= 140737479966720 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 dn_extra)) dn_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_next)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dn_Bx [] (Eimg (Ereg regs1 dn_extra)) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp y Hsp Hs Hs16 R23 Hy.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 dn_extra)).
assert (E2 : ew E 2 = getr regs1 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E23 : ew E 23 = Z_to_bv 64 y)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (U23 : bv_unsigned (ew E 23) = y) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + split; [|split; [|exact I]].
    * unfold dn_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U23, U32.
      assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
        unfold SHADOW_OFF in *; lia.
    * unfold dn_facts. cbn [f_conds conds_ok]. split; [|exact I].
      (* the trap kit's closer for 0x839e0's not-taken edge: s7 is not -1 *)
      apply (trap_seat E BC_EQ (SOff 23 0) (SLit 18446744073709551615)).
      rewrite trap_br_eq, (U_atom E 23 y E23) by lia. rewrite U_lit by lia.
      apply Z.eqb_neq. lia.
- unfold sh_ok. apply Forall_nil.
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

Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let JOIN := dr_memchr_join B MT MMAX RG LAWS HG AMEMCHR HCROM HRGD HGSB HMMAX HV9 HSD HSM.

Theorem dr_next : dr_next_stmt B MT MMAX RG.
Proof.
unfold dr_next_stmt. intros cx s1 D p W1 c1 HB HDLN Kll Klr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDLN as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R23 & HDB & HCAP & Hbnd & Hp0 & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC, LCORE in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & HEOK & _).
pose proof HB as (Hafn & _).
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof HEOK as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & _).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
destruct (dn_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_buf e1 + Z.of_nat p - 1)
  Hsp ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity) R23 ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs1 dn_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_next)) with (Z_to_bv 64 (BASE + A_dr_next)).
paj_run_to_tok RUNTO HS HJ SHOK dn_Bspan A_dr_join; [apply awr_ok_x_of0; awr_ok_tac|].
lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KL : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
{ intros y; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr); vm_compute in Hin; destruct Hin. }
assert (KP : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR1 Hy)).
pose proof (dnk_DMEM_call B MT MMAX RG LAWS HG HRGD HGSB HMMAX HV9 HSD HSM cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 _
  e1 h1 _ out1 ev1 _ LB1 (dsp0 cx - DRAIN_FRAME) HB HM HJ ltac:(lia) (fun y _ _ => KL y) KP) as HMF.
pose proof HMF as (_ & _ & _ & _ & HFRF & _).
pmkst HS.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by exact EREG.
apply (JOIN cx s1 D p W1 _ HB); [|exact Kll | exact Klr].
exists (ms_regs msF), ly1, S1, (ms_mem msF). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line.
  split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
  split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
  split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
  split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
  split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
  split; [rewrite X22, (KEPT 22%nat 22%bv) by (first [lia | reflexivity]); exact R22|].
  split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
  split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
  split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
  split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
  exact HFRF. }
split; [rewrite X26; reflexivity|].
split.
{ rewrite X24, (KEPT 23%nat 23%bv) by (first [lia | reflexivity]). rewrite R23. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal. lia. }
split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
split; [unfold DLC, LCORE; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD))))) | exact HFUT].
Qed.


End c.

(* ---- THE GENERIC WALK (an internal work row): NEXT over any allocator relation ARx with its laws, at the room texts.  The
   Section is W_drain_cx_x.v's Section c - its variables B PST ARx MT RP MMAX RG in that order, each hypothesis that
   file's text - with the allocator rules in their caller-context forms (this segment calls no allocator, so no
   call-site fact HCTX_* is stated), and after LAWS the generic-relation fact HP0 (no hidden head in any ARx state,
   a Theorem Labs lane's ruling; W_drain_join.v's dr_memchr_join_x reads the table's and the buffer's shadow under it).  The AR
   walk above (Section c) is unchanged. ---- *)
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

Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let JOIN := dr_memchr_join_x B PST ARx MT RP MMAX RG LAWS HP0 HG HGO AMEMCHR HCROM HRGD HGSB HMMAX HSD HSM.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): NEXT at a world relation R.  dr_next_stmt_x -> W_drain_cx_x.v's
   dr_next_stmt_xR .. R (R after RG), DLN_x / DLC_x / LCORE_x / DMEM_x -> their R twins, the run -> W_journal_x.v
   paj_run_to_x_xG, dnk_DMEM_call_x -> dnk_DMEM_call_xR, the join -> W_drain_join.v dr_memchr_join_xR.  dr_next_x
   below is it at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let JOINR := dr_memchr_join_xR B PST ARx MT RP MMAX RG LAWS HP0 HG HGO AMEMCHR HCROM HRGD HGSB HMMAX HSD HSM R
  R_trans WLE_R.

(* R twin of dr_next_x *)
Theorem dr_next_xR : dr_next_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_next_stmt_xR. intros cx Hpe kr s1 D p W1 c1 HB HDLN Kll Klr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDLN as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R23 & HDB & HCAP & Hbnd & Hpp0 & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC_xR, LCORE_xR in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & HEOK & _).
pose proof HB as (Hafn & _).
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof HEOK as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & _).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
destruct (dn_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_buf e1 + Z.of_nat p - 1)
  Hsp ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity) R23 ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs1 dn_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_next)) with (Z_to_bv 64 (BASE + A_dr_next)).
paj_run_to_tok_xR RUNTOR HS HJ SHOK dn_Bspan A_dr_join; [apply awr_ok_x_of0; awr_ok_tac|].
lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (KL : forall y, aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y).
{ intros y; apply (aview_eq_of SEGS); apply FR1; intros (r & Hin & Hr); vm_compute in Hin; destruct Hin. }
assert (KP : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR1 Hy)).
pose proof (dnk_DMEM_call_xR B PST ARx MT RP MMAX RG LAWS HG HGO HRGD HGSB HMMAX HSD HSM R cx Hpe kr ly1 S1 Hp1 W1 m1
  (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1 (dsp0 cx - DRAIN_FRAME) HB HM HJ ltac:(lia) (fun y _ _ => KL y) KP)
  as HMF.
pose proof HMF as (_ & _ & _ & _ & HFRF & _).
pmkst HS.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by exact EREG.
apply (JOINR cx Hpe kr s1 D p W1 _ HB); [|exact Kll | exact Klr].
exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl.
split; [reflexivity|].
split.
{ unfold dregs_line.
  split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
  split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
  split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
  split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
  split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
  split; [rewrite X22, (KEPT 22%nat 22%bv) by (first [lia | reflexivity]); exact R22|].
  split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
  split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
  split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
  split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
  exact HFRF. }
split; [rewrite X26; reflexivity|].
split.
{ rewrite X24, (KEPT 23%nat 23%bv) by (first [lia | reflexivity]). rewrite R23. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal. lia. }
split; [exact HDB|]. split; [exact HCAP|]. split; [exact Hbnd|].
split; [unfold DLC_xR, LCORE_xR; exact (conj HMF (conj HL (conj HSAME (conj HH (conj HRS HBUD))))) | exact HFUT].
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* ---- NEXT: DLN 0x839d4 -> the trap-free step to DJ 0x8395c, then the memchr join (DLL p q / DLR p). ---- *)
Theorem dr_next_x : dr_next_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_next_xR (@wle SEGS)); wle_inst.
Qed.

End cx.
End b.
End a.
