(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow_tail.v, with its module paths, module names and numbers changed; 10 of its 428 lines of code are new or changed and 1576 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm, second half, the piece around the call of the PROGRAM
   function fuzz_realloc (A_fuzz_realloc 0x82bc4 = 535492, ra = 0x84580 = 542080):
   - pgt_callee_pre: fuzz_realloc's fpreU at the call (callee sp = put's sp - 112, ra = 542080, gp / tp kept, the frame
     chain from s0 = o built from put_spec's chain clause HCHN);
   - pgt_resume: after fuzz_realloc returns to 0x84580, the caller's journal composed with the callee's, ARU at the
     callee's heads, the bytes at or above put's sp kept, and st_ok of lib/B/FSW_put_grow_tail.v pgt_ss1 at 542080 over
     the env `Ereg regs2 (fs_extraT ++ pgt_xs E' res len c d buf cap)`.
   B MEASUREMENTS (integrator a Theorem Labs lane, 2026-10-29T09:2xZ, lib/B/FSW_put_grow.v fsw_pg_ssc_pc / fsw_pg_ssc_ra and
   lib/B/FSW_put_grow_tail.v pgt_call_regs): the call-site state fsw_pg_ssc is a FETCH stop at 535492 with
   ra = SLit 542080, sp = entry sp - 112, s0 = o, s1 = n, s2 = s, s3 = o >> 3 (x19), s4 = o + 24 (x20), s5 = o + 16,
   s6 = c, s7 = the shadow base, s8 .. s11 = the shadow addresses of o + 8 / o + 24 / o + 16 / o; its frame
   (fsw_pg_cs) holds o + 8 at sp - 112 and the 13 saved words at sp - 104 .. sp - 8. B's s3 / s4 are A's swapped, so
   pgt_resume re-seats x19 = (atom 8) >> 3 and x20 = atom 8 + 24 (pgt_regs1's order). STK_fuzz_realloc + 112 <=
   STK_put is computed (vm_compute), never pinned.
   TAKEN FROM: lib/A/FSW_put_grow_tail.v lines 376-728 (pgt_callee_pre, pgt_resume) at a working branch
   860b2fb1188, with the resume pc 541288 -> 542080 and B's s3 / s4; B kit lemmas: lib/B/FSW_ret.v:191
   fsw_fpreU_atFP, lib/B/FSW_K3.v:70 fsw_ajournal_sub5, lib/B/FSW_K.v:123 fsw_sp, :193 fsw_got_shadow, :575
   arodata_below, :103 fsw_aview_unpoison_high, :109 fsw_apresent_unpoison, lib/B/FSW_put.v:218 fsw_pf_chunk_move.
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

(* ================= piece 1: THE CALLEE'S PRE ================= *)
(* fuzz_realloc's fpreU at the call (FSW_ret.fsw_fpreU_atFP): the callee's sp is sp - 112 inside put's raised window,
   ra = 0x84580, gp / tp kept, and the frame chain from s0 = o built from put_spec's chain clause: o > alloc_ceiling
   (fsw_sp), so a node whose saved next fp is below alloc_ceiling is bad_next and ends the chain. *)
Lemma pgt_callee_pre : exists ch1, fpreU tfibsegs B STK_fuzz_realloc ly S U W (ms_regs ms') (ms_mem ms') mdc ch1.
Proof.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate).
assert (HSTK0 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & _).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms')))
  by exact (arodata_below B W mem (ms_mem ms') SB HRO).
set (rd := aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))).
(* above the frame, the reader at the call is the entry's *)
assert (RDH : forall a, spZ regs <= a < 2 ^ 64 -> rd a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. unfold rd. apply (aview_at tfibsegs). apply pgt_unpoison_at. apply HMF; lia. }
(* the frame's words at the call, read off the call-site state *)
pose proof (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & HRS & _).
cbn [ms_mem restrict] in HRS. apply Forall_inv in HRS.
destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_base YP09.r_chunks base_val] in HCS.
assert (E'2 : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (pgt_E'_reg 2 2%bv) by (lia || reflexivity); reflexivity).
rewrite E'2 in HCS.
rewrite Forall_forall in HCS.
assert (WRA : rdword rd (spZ regs - 8) = Some (raZ regs)).
{ assert (Hc : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms')) (spZ regs)
                 (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))))
    by (apply HCS; repeat (first [left; reflexivity | right])).
  pose proof (val_of_chunk_ok tfibsegs E' _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs) Hc) as Hv.
  assert (Hra64 : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; apply u64_range).
  specialize (Hv ltac:(rewrite fsw_SOff0, (pgt_E'_reg 1 1%bv) by (lia || reflexivity); unfold raZ;
                       symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)).
  replace (spZ regs + -8) with (spZ regs - 8) in Hv by lia.
  rewrite <- (pgt_rdword_of_val_mem (w_H W) (ms_mem ms') (spZ regs - 8) (raZ regs) Hv Hra64).
  apply rdword_ext. intros k Hk. unfold rd.
  apply (fsw_aview_unpoison_high B ly S U W (ms_mem ms') mdc _ HARU). lia. }
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Ho16 : o < ly_top ly - 16) by lia.
assert (HCH1 : exists ch1, achain ly rd (spZ (ms_regs ms')) (s0Z (ms_regs ms')) ch1).
{ unfold s0Z. rewrite R8, R2, (wz o) by lia.
  destruct HCHN as [(Ho & Hral) | (Ho & ra & nfp & Hra' & Hnfp & Hor)].
  - (* o right above put's frame: o - 16 is put's own saved ra *)
    destruct (pgt_rdword_some (w_H W) (unpoison U (ms_mem ms')) (o - 8)) as (v & Hv & Hv0).
    { intros k Hk. fold rd. rewrite RDH by lia.
      apply (aview_some_of_apresent tfibsegs). destruct (HPRESENT (o - 8 + k) ltac:(lia)) as (Hh & b & Hb).
      split; [exact Hh|]. unfold unpoison.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 (o - 8 + k)))); [exists (Z_to_bv 8 0); reflexivity | exists b; exact Hb]. }
    fold rd in Hv.
    destruct (Z_lt_ge_dec v 4096) as [Hv4 | Hv4].
    + exists []. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split; [|constructor].
      cbn [fpchain]. exists v. split; [exact Hv | lia].
    + exists [(o, v, raZ regs)]. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split.
      * cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Hv|].
        split; [replace (o - 16) with (spZ regs - 8) by lia; exact WRA|]. split; [lia|].
        assert (Hb : bad_next o (ly_top ly) (raZ regs) = true)
          by (unfold bad_next; rewrite (proj2 (Z.leb_le (raZ regs) o)) by lia; reflexivity).
        rewrite Hb. exact eq_refl.
      * constructor; [cbn [fst]; lia | constructor].
  - (* the chain from o ends after one node, both words in the caller's frame *)
    assert (Rd8 : rdword rd (o - 8) = Some ra) by (rewrite <- Hra'; apply rdword_ext; intros k Hk; apply RDH; lia).
    assert (Rd16 : rdword rd (o - 16) = Some nfp) by (rewrite <- Hnfp; apply rdword_ext; intros k Hk; apply RDH; lia).
    pose proof (pgt_rdword_nonneg _ _ _ _ Hra') as Hra0.
    destruct (Z_lt_ge_dec ra 4096) as [Hr4 | Hr4].
    + exists []. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split; [|constructor].
      cbn [fpchain]. exists ra. split; [exact Rd8 | lia].
    + destruct Hor as [Hor | Hor]; [lia|].
      exists [(o, ra, nfp)]. right. split; [lia|]. split; [exact Ho16|]. split; [exact Ho8|]. split.
      * cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Rd8|]. split; [exact Rd16|].
        split; [lia|].
        assert (Hb : bad_next o (ly_top ly) nfp = true)
          by (unfold bad_next; rewrite (proj2 (Z.leb_le nfp o)) by lia; reflexivity).
        rewrite Hb. reflexivity.
      * constructor; [cbn [fst]; lia | constructor]. }
destruct HCH1 as (ch1 & HCH1). exists ch1.
apply (fsw_fpreU_atFP B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W (unpoison U mem) md []
  ly S W (ms_mem ms') mdc 0 (ms_regs ms') STK_fuzz_realloc (spZ regs - 112 - ot) ch1 HJ HARU HRO').
- rewrite R2. lia.
- lia.
- lia.
- exact HSTK0.
- lia.
- unfold YK0s.ret_ok. rewrite R1. apply bv_eq. vm_compute. reflexivity.
- unfold raZ. rewrite R1, wz; lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- exact HCH1.
Qed.

(* ================= piece 2: THE RESUME ================= *)
(* fuzz_realloc has returned to 0x84580: the caller's journal (window top ot) composed with the callee's
   (FSW_K3.fsw_ajournal_sub5, the callee's FP1 under fsw_fp_sub), ARU at the callee's heads U2, and the resume state
   pgt_ss1 on the memory after the call. FSW_K3.fsw_after_callFPU_args ties the frame top to the journal top sp0;
   put's journal top is ot > sp, so the state is built here with entry_st_ok_full as that lemma builds its own
   (FSW_K3.v:390-431): the frame's 14 words and o's len / failed fields read off the call site and kept by the
   callee journal's frames clause (at or above alloc_ceiling, outside [sp - 112 - STK_fuzz_realloc, sp - 112)), the
   shadow-base cells from AR, then the nine re-seated callee-saved registers (st_ok_set_reg). *)
Lemma pgt_resume : forall FP1 kc ly2 S2 U2 W2 regs2 mem2 md2 res d,
  ajournal tfibsegs B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S W (unpoison U (ms_mem ms')) mdc []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap) FP1 ->
  upoison_ok B ly2 S2 U2 -> upoisoned tfibsegs W2 mem2 U2 ->
  aregs_preserved (ms_regs ms') regs2 ->
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc /\
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 /\
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) /\
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' res (Z.of_nat (length text)) c d buf cap)) pgt_ss1
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs))).
Proof.
intros FP1 kc ly2 S2 U2 W2 regs2 mem2 md2 res d HJc HFP OK2 PO2 HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate).
assert (HSTK0 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp16 & HSTKa & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct pgt_call_regs as (Ems & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R18 & R22 & R23 & R19 & R20 & R21 &
  R24 & R25 & R26 & R27).
assert (E'10 : ew E' 10 = Z_to_bv 64 o) by (rewrite (pgt_E'_reg 10 10%bv) by (lia || reflexivity); exact G10).
assert (E'32 : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (pgt_E'_x 32) by lia; reflexivity).
assert (E'2 : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (pgt_E'_reg 2 2%bv) by (lia || reflexivity); reflexivity).
(* the composed journal and ARU after the call *)
assert (HJ2 : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
    (unpoison U mem) md [] ly2 S2 W2 (unpoison U2 mem2) md2 kc).
{ pose proof (fsw_ajournal_sub5 B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
    (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms')) mdc 0 STK_fuzz_realloc (spZ (ms_regs ms')) FP1 []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc HJ HJc ltac:(rewrite R2; lia) ltac:(rewrite R2; lia) HFP) as H.
  rewrite Z.add_0_l in H. exact H. }
assert (HARU2 : ARU tfibsegs B ly2 S2 U2 W2 mem2 md2) by (split; [exact (proj1 HJ2) | split; [exact OK2 | exact PO2]]).
split; [exact HJ2|]. split; [exact HARU2|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
(* every byte at or above put's frame is the call's after fuzz_realloc, and at or above sp the entry's *)
assert (KEEPC : forall a, spZ regs - 112 <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly2 S2 U2 W2 mem2 md2 a HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms') mdc a HARU) by lia.
  apply F1; [lia | rewrite R2; lia]. }
assert (KEEPE : forall a, spZ regs <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. rewrite (KEEPC a) by lia. unfold mbyte, mrestrict. rewrite (HMF a) by lia. reflexivity. }
split; [exact KEEPE|].
(* the frame words at the call *)
pose proof (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & HRS & _).
cbn [ms_mem restrict] in HRS. apply Forall_inv in HRS.
destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_base YP09.r_chunks base_val] in HCS.
rewrite E'2 in HCS. rewrite Forall_forall in HCS.
set (len := Z.of_nat (length text)) in *.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' res len c d buf cap)).
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms') 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112).
{ unfold Er. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2. exact R2. }
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F9 : ew Er 9 = Z_to_bv 64 n) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9; exact R9).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F35 : ew Er 35 = Z_to_bv 64 c) by (unfold Er; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F50 : ew Er 50 = Z_to_bv 64 buf)
  by (unfold Er; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F51 : ew Er 51 = Z_to_bv 64 cap)
  by (unfold Er; change 51%nat with (32 + 19)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
assert (F9u : bv_unsigned (ew Er 9) = n) by (rewrite F9; apply wz; unfold WMAX in *; lia).
assert (F32u : bv_unsigned (ew Er 32) = SHADOW_OFF) by (rewrite F32; apply wz; unfold SHADOW_OFF; lia).
assert (F34u : bv_unsigned (ew Er 34) = len) by (rewrite F34; apply wz; unfold WMAX in *; lia).
assert (F35u : bv_unsigned (ew Er 35) = c) by (rewrite F35; apply wz; unfold WMAX in *; lia).
(* a saved word of the call's frame is the resume frame's chunk *)
assert (CM : forall o0 (k j : nat), ew Er j = ew E' k ->
  YP09.chunk_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms')) (spZ regs) (YP09.mkChunk o0 (CVal 8 (SOff k 0))) ->
  -112 <= o0 -> o0 + 8 <= 0 ->
  YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) mem2) (spZ regs - 112) (YP09.mkChunk (o0 + 112) (CVal 8 (SOff j 0)))).
{ intros o0 k j Hjk Hck Ho1 Ho2.
  apply (fsw_pf_chunk_move E' Er _ _ (spZ regs) (spZ regs - 112) o0 (o0 + 112) 8 (SOff k 0) (SOff j 0) Hck).
  - rewrite !fsw_SOff0. exact Hjk.
  - lia.
  - intros i Hi. cbn [Z.of_N] in Hi. apply KEEPC. lia. }
assert (C0 : YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) mem2) (spZ regs - 112) (YP09.mkChunk 0 (CVal 8 (SOff 8 8)))).
{ apply (fsw_pf_chunk_move E' Er _ _ (spZ regs) (spZ regs - 112) (-112) 0 8 (SOff 10 8) (SOff 8 8)
    (HCS (YP09.mkChunk (-112) (CVal 8 (SOff 10 8))) ltac:(repeat (first [left; reflexivity | right])))).
  - cbn [sv_denot]. rewrite F8, E'10. reflexivity.
  - lia.
  - intros i Hi. cbn [Z.of_N] in Hi. apply KEEPC. lia. }
(* the shadow-base cells on the memory after the call (as FSW_put.v:985-1003) *)
destruct (fsw_got_shadow B ly2 S2 W2 (unpoison U2 mem2) md2 (proj1 HSS) (proj2 HSS) (proj1 HARU2)) as [Kgot Kcell].
assert (MBL : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) x = mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly2 S2 U2 W2 mem2 md2 (Z_to_bv 64 x) HARU2
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MBL (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W2) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W2) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem2) _ _ Kcell)]. }
(* the resume state with every register its own atom *)
assert (HSR0 : st_ok tfibsegs Er
    (mkSS 542080 sr_atoms (fsT_ret_regions 112 pgt_cs1 [pgt_o1]) None
      (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: pgt_gf1) [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); fold Er.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold fsT_ret_regions. cbn [app].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + (* the frame, its 14 words *)
      unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite F2. split; [lia|]. split; [lia|]. split.
      * intros q Hq. apply (apresent_writable tfibsegs).
        apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2); [lia|]. apply Hpres2. lia.
      * unfold pgt_cs1, fsw_pf_cs. constructor; [exact C0|].
        repeat constructor.
        all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o2 (CVal 8 (SOff ?j 0))) =>
          let o0 := eval vm_compute in (o2 - 112) in
          let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                       else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
          exact (CM o0 k j eq_refl (HCS (YP09.mkChunk o0 (CVal 8 (SOff k 0)))
                   ltac:(repeat (first [left; reflexivity | right]))) ltac:(lia) ltac:(lia))
        end.
    + (* the GOT word of the shadow base *)
      unfold fs_got_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
      split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
        (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
        [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
    + (* the shadow-base cell *)
      unfold fs_bcell_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
      split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
        [rewrite fsw_SOff0, F32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
    + (* o: its len and failed fields, all 32 bytes writable *)
      unfold pgt_o1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite F8u. split; [lia|]. split; [lia|]. split.
      { intros q Hq. apply (apresent_writable tfibsegs).
        apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2); [lia|]. apply Hpres2. lia. }
      assert (VH2 : forall a k v, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
        val_mem tfibsegs (mrestrict (w_H W) mem) a k v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v)
        by (intros a k v Ha Hk Hv i Hi; rewrite (KEEPE (a + Z.of_nat i)) by lia; exact (Hv i Hi)).
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val tfibsegs Er _ o 0 8 (SOff 50 0) buf);
          [rewrite fsw_SOff0; exact F50 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | rewrite Z.add_0_r; exact (VH2 o 8%nat buf ltac:(lia) ltac:(lia) Vbuf)].
      * apply (chunk_ok_val tfibsegs Er _ o 8 8 (SOff 34 0) len);
          [rewrite fsw_SOff0; exact F34 | cbn [Z.of_N]; unfold WMAX in *; lia | cbn [Z.of_N]; lia
          | exact (VH2 (o + 8) 8%nat len ltac:(lia) ltac:(lia) Vlen)].
      * apply (chunk_ok_val tfibsegs Er _ o 16 8 (SOff 51 0) cap);
          [rewrite fsw_SOff0; exact F51 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | exact (VH2 (o + 16) 8%nat cap ltac:(lia) ltac:(lia) Vcap)].
      * apply (chunk_ok_val tfibsegs Er _ o 24 4 (SLit 0) 0);
          [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact (VH2 (o + 24) 4%nat 0 ltac:(lia) ltac:(lia) Vfail)].
  - apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pgt_o1, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F2, F8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok pgt_gf1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite F2, F32u, F8u, F34u, F35u, F9u.
    change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold WMAX in *. repeat split; lia. }
(* the nine callee-saved registers the post-call code reads, re-seated over atoms 8 / 32 / 35 *)
assert (P19 : getr regs2 19%bv = getr (ms_regs ms') 19%bv) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20%bv = getr (ms_regs ms') 20%bv) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21%bv = getr (ms_regs ms') 21%bv) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22%bv = getr (ms_regs ms') 22%bv) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23%bv = getr (ms_regs ms') 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24%bv = getr (ms_regs ms') 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25%bv = getr (ms_regs ms') 25%bv) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26%bv = getr (ms_regs ms') 26%bv) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27%bv = getr (ms_regs ms') 27%bv) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
assert (NZ : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv)
  by (intros r Hr Hz; apply Hr; rewrite Hz; reflexivity).
assert (Q19 : getr regs2 19%bv = sv_denot Er (SAlu ALU_SRL (SOff 8 0) (SLit 3))).
{ rewrite P19, R19. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q20 : getr regs2 20%bv = sv_denot Er (SOff 8 24)).
{ rewrite P20, R20. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q21 : getr regs2 21%bv = sv_denot Er (SOff 8 16)).
{ rewrite P21, R21. cbn [sv_denot]. rewrite E'10, F8. reflexivity. }
assert (Q22 : getr regs2 22%bv = sv_denot Er (SOff 35 0)) by (rewrite P22, R22, fsw_SOff0, F35; reflexivity).
assert (Q23 : getr regs2 23%bv = sv_denot Er (SOff 32 0)) by (rewrite P23, R23, fsw_SOff0, F32; reflexivity).
assert (Q24 : getr regs2 24%bv = sv_denot Er (pgt_sh 8)).
{ rewrite P24, R24. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q25 : getr regs2 25%bv = sv_denot Er (pgt_sh 24)).
{ rewrite P25, R25. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q26 : getr regs2 26%bv = sv_denot Er (pgt_sh 16)).
{ rewrite P26, R26. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (Q27 : getr regs2 27%bv = sv_denot Er (pgt_sh 0)).
{ rewrite P27, R27. unfold pgt_sh. cbn [sv_denot]. rewrite E'10, E'32, F8, F32. reflexivity. }
assert (N19 : 19%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N20 : 20%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N21 : 21%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N22 : 22%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N23 : 23%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N24 : 24%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N25 : 25%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N26 : 26%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
assert (N27 : 27%bv <> 0%bv :> bv 5) by (apply NZ; vm_compute; discriminate).
(* one register at a time, the state's projections reduced after each step: st_ok_set_reg's conclusion repeats the
   state five times (ss_pc / ss_regs / ss_mem / ss_resv / ss_facts), so nine unreduced steps grow it as 5 ^ 9 *)
pose proof (st_ok_set_reg tfibsegs Er _ _ 19%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)) HSR0 N19 Q19) as H19.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H19. clear HSR0.
pose proof (st_ok_set_reg tfibsegs Er _ _ 20%bv (SOff 8 24) H19 N20 Q20) as H20.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H20. clear H19.
pose proof (st_ok_set_reg tfibsegs Er _ _ 21%bv (SOff 8 16) H20 N21 Q21) as H21.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H21. clear H20.
pose proof (st_ok_set_reg tfibsegs Er _ _ 22%bv (SOff 35 0) H21 N22 Q22) as H22.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H22. clear H21.
pose proof (st_ok_set_reg tfibsegs Er _ _ 23%bv (SOff 32 0) H22 N23 Q23) as H23.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H23. clear H22.
pose proof (st_ok_set_reg tfibsegs Er _ _ 24%bv (pgt_sh 8) H23 N24 Q24) as H24.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H24. clear H23.
pose proof (st_ok_set_reg tfibsegs Er _ _ 25%bv (pgt_sh 24) H24 N25 Q25) as H25.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H25. clear H24.
pose proof (st_ok_set_reg tfibsegs Er _ _ 26%bv (pgt_sh 16) H25 N26 Q26) as H26.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H26. clear H25.
pose proof (st_ok_set_reg tfibsegs Er _ _ 27%bv (pgt_sh 0) H26 N27 Q27) as H27.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H27. clear H26.
exact H27.
Qed.


End pgt.
