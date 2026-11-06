(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow_tail.v, with its module paths, module names and numbers changed; 9 of its 316 lines of code are new or changed and 1687 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm, second half, the piece pgt_refused: fuzz_realloc answered
   NULL (a0 = 0), put stores 1 into o->failed and returns; its post is put_spec's fpostU with o's failed = 1.
   B MEASUREMENTS (integrator a Theorem Labs lane, token engine on B, 2026-10-29T09:2xZ): from lib/B/FSW_put_grow_tail.v
   pgt_ss1 (run_K 52, sh_static_ok true, regions_wf true; SH = pgt_SH1 = [mkSHE 8 0 32]) the run stops at once at
   542080 = 0x84580, SR_branch BC_EQ (SOff 10 0) (SLit 0) (`beqz a0`). Its TAKEN side (a0 = 0) passes the inline
   shadow check of o + 24 at 0x8466c / 0x84670 (report site 0x846b4) through pgt_SH1, stores 1 (4 bytes) at o + 24,
   restores the frame and stops at the ret 542312 = 0x84668 (A: 541460 = 0x84314), SR_jalr (SOff 37 0), sh_obls = [];
   final regs ra = SOff 37 0, sp = SOff 2 112, s0 = SOff 38 0, s1 = SOff 39 0, a0 = SLit 1, s2 .. s11 = SOff 40 .. 49 0.
   TAKEN FROM: lib/A/FSW_put_grow_tail.v lines 1367-1594 (pgt_refused) at a working branch 860b2fb1188,
   with the resume pc 541288 -> 542080 and the ret 541460 -> 542312; B kit: lib/B/FSW_K.v:1450 fsw_aj_run_tokU, :691
   fsw_preserved, :109 fsw_apresent_unpoison, :123 fsw_sp, lib/B/FSW_ret.v:162 fsw_retU, lib/Reusable/YCbm.v:239
   srr_branch_tok, lib/Reusable/YCbq.v:2189 awr_ok_cons_stack_off, :2176 awr_ok_cons_ro, :2715 shent_ok_of_range,
   lib/A/FSupoisonStack.v:89 fsw_ARU_stack_ra.
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_put FSW_put_grow FSW_put_grow_model FSW_put_grow_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section pgt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0's shadow-base cells (lib/B/FSH_Base.v FsShadowSyms), the one interceptor contract the granted path calls
   (__asan_memcpy, lib/B/FSH_Rt.v FsRt's fr_memcpy field, as lib/B/FSW_put.v takes it) and the image facts *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* THE CALLEE: fuzz_realloc's ASan contract, a statement only (lib/B/FSH_Fn_alloc.v, by path from dda8331bd25:
   CTX-free with its `cnt <> fail ->` room guards), discharged at composition. *)
Hypothesis HREALLOC : fuzz_realloc_spec tfibsegs B.

(* ---- put_spec's data, on the grow arm (failed = 0, cap < len + n + 1) ---- *)
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (ot o s n buf cap : Z) (text bs : list Z)
  (live peak cnt fail : Z).
Hypothesis HPRE : fpreU tfibsegs B STK_put ly S U W regs mem md ch.
Hypothesis FH : fs_heads B ly S U.
Hypothesis HHEAD : cap <> 0 -> In (buf - HEAD, HEAD) U.
Hypothesis G10 : getr regs 10 = w64 o.
Hypothesis G11 : getr regs 11 = w64 s.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis HOUT : wout_ok B tfibsegs ly S W mem o buf cap 0 text.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis Hspo : spZ regs <= o.
Hypothesis Hoot : o + 32 <= ot.
Hypothesis Hot16 : ot mod 16 = 0.
Hypothesis Hottop : ot <= ly_top ly.
Hypothesis HCHN :
  o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
  spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
    rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling).
Hypothesis HPRESENT : forall a, spZ regs <= a < ot -> apresent (w_H W) mem a.
Hypothesis HZS : zbytes_at tfibsegs W mem s bs.
Hypothesis HSK : wsrc_kept B tfibsegs ly S U W mem buf s bs.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hbok : WriterSpec.bytes_ok bs.
Hypothesis HSRC : 0 <= s /\ s + n <= alloc_ceiling.
Hypothesis Hsdisj : s + n <= o \/ ot <= s.
Hypothesis HWM : Z.of_nat (length text) + n + 1 <= WMAX.
Hypothesis HCAP : cap <= WMAX.
Hypothesis HCL : cap <= live.
Hypothesis HBUD : wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs).
Hypothesis HGROW : cap < Z.of_nat (length text) + n + 1.

(* ---- the first half's hand-over, at the call of fuzz_realloc (lib/B/FSW_put_grow_run.v fsw_pg_to_call's
   continuation; A's Theorem Labs lane interface) ---- *)
Variables (E' : env) (ms' : machine_state) (mdc : Model) (c : Z).
Hypothesis HS : st_ok tfibsegs E' fsw_pg_ssc (restrict (w_H W) ms').
Hypothesis HJ : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
  ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms')) mdc 0.
Hypothesis HARU : ARU tfibsegs B ly S U W (ms_mem ms') mdc.
Hypothesis HMF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
  ms_mem ms' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Hypothesis HPRK : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a.
Hypothesis HEA : YP06.env_agree 36
  (Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])) E'.
Hypothesis HE36 : ew E' 36 = Z_to_bv 64 c.
Hypothesis Hcnew : c = WriterSpec.newcap cap (Z.of_nat (length text) + n + 1).
Hypothesis Hc4096 : 4096 <= c.
Hypothesis HcW : c <= WMAX.
Hypothesis Hcneed : Z.of_nat (length text) + n + 1 <= c.

(* the tail file's call-site lemmas, re-stated over this Section's data (lib/B/FSW_put_grow_tail.v closes its
   Section, so its lemmas take the Section data as arguments; these copies keep A's proof text unchanged) *)
Lemma pgt_E'_reg : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E' j = getr regs r.
Proof. intros j r Hj Hr. eapply FSW_put_grow_tail.pgt_E'_reg; eassumption. Qed.
Lemma pgt_E'_x : forall (j : nat), (32 <= j < 36)%nat ->
  ew E' j = nth (j - 32) (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])
              (Z_to_bv 64 0).
Proof. intros j Hj. eapply FSW_put_grow_tail.pgt_E'_x; eassumption. Qed.
Lemma pgt_call_regs :
  ms' = mkst (ms_regs ms') (Z_to_bv 64 A_fuzz_realloc) (ms_mem ms') (seg_rom tfibsegs) /\
  getr (ms_regs ms') 1%bv = Z_to_bv 64 542080 /\ spZ (ms_regs ms') = spZ regs - 112 /\
  getr (ms_regs ms') 3%bv = getr regs 3%bv /\ getr (ms_regs ms') 4%bv = getr regs 4%bv /\
  getr (ms_regs ms') 8%bv = Z_to_bv 64 o /\ getr (ms_regs ms') 9%bv = Z_to_bv 64 n /\
  getr (ms_regs ms') 10%bv = w64 buf /\ getr (ms_regs ms') 11%bv = w64 c /\
  getr (ms_regs ms') 18%bv = Z_to_bv 64 s /\ getr (ms_regs ms') 22%bv = Z_to_bv 64 c /\
  getr (ms_regs ms') 23%bv = Z_to_bv 64 SHADOW_OFF /\
  getr (ms_regs ms') 19%bv = sv_denot E' (SAlu ALU_SRL (SOff 10 0) (SLit 3)) /\
  getr (ms_regs ms') 20%bv = sv_denot E' (SOff 10 24) /\
  getr (ms_regs ms') 21%bv = sv_denot E' (SOff 10 16) /\
  getr (ms_regs ms') 24%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 25%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 26%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0)) /\
  getr (ms_regs ms') 27%bv = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)).
Proof. eapply FSW_put_grow_tail.pgt_call_regs; eassumption. Qed.

(* ================= piece 4: THE REFUSED TAIL ================= *)
(* fuzz_realloc answered NULL (its cnt = fail arm: heads U kept, blocks unchanged, journal 0). From the resume state
   `beqz a0` is taken: put stores 1 into o->failed (4 bytes at o + 24) and returns (MEASURED: the run stops at the ret
   542312 = 0x84668, sh_obls = [], after the shadow check of o + 24 at 0x8466c / 0x84670). o's buf / len / cap fields
   are read back off the resume state's chunks (atoms 50, 34, 51), the buffer's facts off the memory after the call. *)
Lemma pgt_refused : forall kc ly2 S2 W2 regs2 mem2 md2 d K,
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' 0 (Z.of_nat (length text)) c d buf cap)) pgt_ss1
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs))) ->
  aregs_preserved (ms_regs ms') regs2 ->
  getr regs2 10%bv = w64 0 ->
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  ((cap = 0 /\ buf = 0 /\ text = []) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly2 S2 W2 mem2 buf cap /\
    Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W2 mem2 buf (text ++ [0]))) ->
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) ->
  fs_glob tfibsegs W2 mem2 live peak (cnt + 1) SIZE_MAXZ ->
  kc <= K ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md K U
      (fun ly' S' W' regs' mem' md' =>
         ly' = ly2 /\ S' = S2 /\
         wout_ok B tfibsegs ly' S' W' mem' o buf cap 1 text /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ /\
         (forall i, 0 <= i < n ->
            mbyte tfibsegs (mrestrict (w_H W') mem') (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))).
Proof.
intros kc ly2 S2 W2 regs2 mem2 md2 d K HJ2 HARU2 HS1 HP R10 KEEPE HCASE2 SKEEP HGLOB2 HKK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 112 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HARU2 as HARU2m.
pose proof HSRC as (Hs0 & Hsn).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10c & R11 & R18 & R22 & R23 & R19 & R20 & R21 &
  R24 & R25 & R26 & R27).
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
unfold WMAX in HWM, HCAP, HcW.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' 0 len c d buf cap)) in *.
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms') 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms') 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112)
  by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; exact R2).
assert (F3 : ew Er 3 = getr regs 3%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl), P3; exact R3).
assert (F4 : ew Er 4 = getr regs 4%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl), P4; exact R4).
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F10 : ew Er 10 = Z_to_bv 64 0) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F50 : ew Er 50 = Z_to_bv 64 buf)
  by (unfold Er; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F51 : ew Er 51 = Z_to_bv 64 cap)
  by (unfold Er; change 51%nat with (32 + 19)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
(* o's 32 bytes addressable over U at ly2 (as in pgt_granted) *)
assert (HLO2 : layout_ok ly2) by exact (am_layout _ _ _ _ (proj1 (proj1 HARU2))).
pose proof (lo_top ly2 HLO2) as LTOP.
assert (Hlo8 : ly_stk_lo ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly2 mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
assert (HRA32 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF o 32).
{ assert (HZS0 : zero_shadow (aview tfibsegs (w_H W2) (unpoison U mem2)) SHADOW_OFF
                  (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2)).
  { exact (al_zshadow _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2
             (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) (proj1 HARU2) (or_introl eq_refl)). }
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly2 S2 U W2 mem2 md2 (w_H W2) o 32 HARU2 ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W2) (unpoison U mem2)) SHADOW_OFF
               (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK1 : sh_ok tfibsegs fs_Bx pgt_SH1 Er (mrestrict (w_H W2) mem2)).
{ unfold pgt_SH1. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W2) mem2 Er fs_Bx 8%nat o 32 o 0 32 HRA32).
  - unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
  - apply (U_atom Er 8 o F8). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* `beqz a0`: a0 = 0, taken *)
srr_branch_tok fsw_put_tbl_ok HS1 SHOK1 fs_Bspan.
2: { exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom Er 10 0 F10) in Hc by lia.
     assert (U0 : YP0e.U Er (SLit 0) = 0) by reflexivity. rewrite U0 in Hc. cbn in Hc. discriminate Hc. }
(* the run: the shadow check of o + 24, o->failed = 1, the epilogue, to the ret 0x84668 *)
fsw_aj_run_tokU fsw_put_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
- lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil.
- assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha H1 H2. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
  pose proof (fun a => apresent_grows _ _ _ a HG) as PRF.
  assert (FR1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
  { pf_reg HS1. rewrite fsw_SOff0. change (ew Er 37) with (ew E' 1). apply pgt_E'_reg; [lia | reflexivity]. }
  (* o's fields, read off the final state *)
  pose proof (st_ok_mem_ok tfibsegs _ _ _ HS1) as (_ & HRSF & _).
  cbn [ms_mem restrict ss_mem] in HRSF.
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRSF.
  destruct HRSF as (_ & _ & _ & HCO). cbn [YP09.r_base YP09.r_chunks base_val] in HCO.
  rewrite F8u in HCO. rewrite Forall_forall in HCO.
  assert (VB : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 0) 8 buf).
  { apply (val_of_chunk_ok tfibsegs _ _ o 0 8 (SOff 50 0) buf
      (HCO (YP09.mkChunk 0 (CVal 8 (SOff 50 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F50 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VL : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 8) 8 len).
  { apply (val_of_chunk_ok tfibsegs _ _ o 8 8 (SOff 34 0) len
      (HCO (YP09.mkChunk 8 (CVal 8 (SOff 34 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F34 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VC : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 16) 8 cap).
  { apply (val_of_chunk_ok tfibsegs _ _ o 16 8 (SOff 51 0) cap
      (HCO (YP09.mkChunk 16 (CVal 8 (SOff 51 0))) ltac:(repeat (first [left; reflexivity | right]))));
      [rewrite fsw_SOff0; exact F51 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  assert (VF : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (o + 24) 4 1).
  { apply (val_of_chunk_ok tfibsegs _ _ o 24 4 (SLit 1) 1
      (HCO (YP09.mkChunk 24 (CVal 4 (SLit 1))) ltac:(repeat (first [left; reflexivity | right]))));
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
  (* every other byte: kept *)
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a H0 H1 H2; unfold mbyte, mrestrict; rewrite (MF a H0 H1 H2); reflexivity).
  assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a)
    by (intros a Ha Ho; rewrite (KF a) by lia; exact (KEEPE a Ha)).
  assert (KL : forall a, 0 <= a < alloc_ceiling ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a Ha; apply KF; lia).
  assert (VL2 : forall a k v, 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
    val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a k v)
    by (intros a k v Ha Hk Hv i Hi; rewrite (KL (a + Z.of_nat i) ltac:(lia)); exact (Hv i Hi)).
  (* the return *)
  eapply (fsw_retU B fsw_put_tbl fsw_put_tbl_ok).
  + exact HS1.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + rewrite FR1. exact Hra.
  + eapply ajournal_mono_k; [exact HJ2 | exact HKK].
  + exact HARU2.
  + lazymatch type of HS1 with
    | st_ok _ ?Ef ?ssf _ =>
      apply (fsw_preserved (w_H W2) Ef ssf _ regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HS1);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end;
    cbv beta;
    lazymatch goal with
    | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
    end;
    first
    [ rewrite denot_lit_U, U_SOff, F2, zcanon_id by (unfold M64; lia);
      replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
    | rewrite fsw_SOff0; exact F3
    | rewrite fsw_SOff0; exact F4
    | lazymatch goal with |- sv_denot _ (SOff ?j 0) = _ =>
        let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                     else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
        rewrite fsw_SOff0; change (ew Er j) with (ew E' k); apply pgt_E'_reg; [lia | vm_compute; reflexivity]
      end ].
  + intros matq.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [lia|]. split.
      { intros i Hi.
        assert (Hp : apresent (w_H W2) mem2 (o + i)).
        { apply (fsw_apresent_unpoison B ly2 S2 U W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia. }
        pose proof (PRF _ Hp) as Hp'. split; [exact (apresent_writable tfibsegs _ _ _ Hp') | exact Hp']. }
      split; [exact Hbuf64|]. split; [exact Hcap64|].
      split; [rewrite Z.add_0_r in VB; exact VB|].
      split; [exact VL|]. split; [exact VC|]. split; [exact VF|].
      split; [right; reflexivity|]. split; [exact Htok|].
      destruct HCASE2 as [Hz | (Hj & HRB2 & Hlt & HZB2)]; [left; exact Hz | right].
      pose proof HRB2 as (Hin2 & Hb16 & Hc0 & Vhead).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 (buf - HEAD) (cap + HEAD) (proj1 HARU2m) Hin2)
        as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
      split; [exact Hj|]. split; [|split; [exact Hlt|]].
      - unfold fs_rblock. split; [exact Hin2|]. split; [exact Hb16|]. split; [exact Hc0|].
        apply (VL2 (buf - HEAD) 8%nat cap); [unfold HEAD in *; lia | unfold HEAD in *; lia | exact Vhead].
      - unfold zbytes_at in HZB2 |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) HZB2).
        intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KL. unfold HEAD in *. lia. }
    split.
    { intros a Ha Hno. split; [apply KH; lia|].
      split; intros _.
      - apply (apresent_writable tfibsegs). apply PRF.
        apply (fsw_apresent_unpoison B ly2 S2 U W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia.
      - apply (apresent_writable tfibsegs). apply HPRESENT. lia. }
    split.
    { unfold fs_glob, fs_glob_at in HGLOB2 |- *. destruct HGLOB2 as (GL1 & GL2 & GL3 & GL4 & GR).
      split; [apply VL2; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact GL1]|].
      split; [apply VL2; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact GL2]|].
      split; [apply VL2; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact GL3]|].
      split; [apply VL2; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact GL4]|].
      exact GR. }
    intros i Hi. rewrite <- (SKEEP i Hi). apply KL. lia.
Qed.


End pgt.
