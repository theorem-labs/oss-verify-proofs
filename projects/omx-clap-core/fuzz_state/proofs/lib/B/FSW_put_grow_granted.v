(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow_tail.v, with its module paths, module names and numbers changed; 128 of its 812 lines of code are new or changed and 1310 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm, second half, the piece pgt_granted: fuzz_realloc granted
   the new buffer res (a0 <> 0); put stores it into o, re-joins the FAST arm's code at 0x845a0 and runs it, through the
   call of __asan_memcpy, to the ret 0x84668. Composed by lib/B/FSW_put_grow_close.v pgt_run (the integrator's).

   The route, MEASURED with the token engine on B (scratch probe lib/B/ZZpbg_granted.v, never committed; a build machine,
   workspace (internal path) at c33a9d6a7d4, 2026-10-29T09:48Z; Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan,
   SH := pgt_SH1 = [mkSHE 8 0 32] until the copy, fsw_pf_SH2 after it; every run ends with sh_obls = [], sh_j = 0
   except run 5, as put_fast_run's):
   - pgt_ss1 (pc 542080 = 0x84580) stops at once at `beqz a0`; its taken side (a0 = 0) is refuted from a0 = res <> 0;
   - run 1 (K 52): the checks of o (0x84584 / 0x84588, report site 0x846f4) and o + 16 (0x84590 / 0x84594, site
     0x846fc), the stores o->buf = a0 and o->cap = c, the reload s6 = o + 8 from frame slot 0, the checks of o (0x845a8,
     site 0x846cc) and o + 8 (0x845b0, site 0x846d4); stop at 542144 = 0x845c0,
     SR_branch BC_LTU (SAlu ALU_ADD (SOff 10 0) (SOff 34 0)) (SOff 10 0); o's region then holds
     [0: SOff 10 0; 8: SOff 34 0; 16: SOff 35 0; 24: CVal 4 (SLit 0)]. The taken side (UBSan's trap 0x84680) is
     refuted from res + len < 2 ^ 64;
   - run 2 (K 50): stop at 542160 = 0x845d0, SR_branch BC_EQ (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 10 0))
     (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 34 0)) (SLit 1))) (SLit 0) (the fast arm's run passes it, as its
     buffer atom 33 carries af_lo 4096; here atom 10 carries no fact). The taken side (trap 0x84680) is refuted from
     res <> 0 and res + len >= res;
   - run 3 (K 50): to the FETCH of __asan_memcpy 335248 = 0x51d90 with ra = 542176 = 0x845e0 (the fast arm's return
     pc), a0 = res + len, a1 = s2 = s, a2 = s1 = n, s8 / s11 = the shadow addresses of o + 8 / o over atom 8;
   - after the copy the state is lib/B/FSW_put.v fsw_pf_ssr with buf := res, cap := c (atom 8 = o, 33 = res,
     34 = len, 35 = c, 36 = res + len + n): run 4 stops at 542212 = 0x84604, SR_branch BC_LTU (SOff 36 0) (SOff 33 0)
     (measured), passing the checks 0x845e4 (site 0x846dc) and 0x845f8 (site 0x846e4); its taken side is refuted from
     res + len + n >= res; run 5 passes 0x84614 / 0x84618 and the store check 0x84628 / 0x8469c (site 0x846a0) and
     stops at the ret 542312 = 0x84668.
   The new buffer is a temporary block of the journal (in the blocks after fuzz_realloc, not in the entry's: awr_byte's
   in_tmp_block arm), where the fast arm's buffer was the old one under wbuf_fp.

   TAKEN FROM: lib/A/FSW_put_grow_tail.v lines 729-1366 at a working branch 860b2fb1188 (pgt_granted:
   the setup, the journal / ARU / wout_ok / fs_glob reasoning, the call, the resume, the post), with B's resume pc,
   memcpy return pc and runs; lib/B/FSW_put.v put_fast_run (unchanged from c33a9d6a7d4 to fa27ae02467): the refutation
   of 0x845c0 :866-873, the call's s8 / s11 :915-919, the three re-seated registers of fsw_pf_ssr :1193-1217, run 4
   :1239-1264, the refutation of 0x84604 :1265-1270, run 5 :1271-1296.
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

(* ================= piece 3: THE GRANTED TAIL ================= *)
(* fuzz_realloc granted the new buffer res (its p = 0 or p <> 0 arm). From the resume state `beqz a0` falls through,
   put stores o->buf = res and o->cap = c, reloads o + 8 from frame slot 0, re-joins the fast arm's code at 0x845a0
   (UBSan's checks 0x845c0 / 0x845d0) and calls __asan_memcpy (res + len, s, n); after the copy the fast arm's resume
   state FSW_put.fsw_pf_ssr applies with buf := res, cap := c, and its runs store len + n at o + 8 and the 0 at
   res + len + n and return. Template: lib/B/FSW_put.v put_fast_run :866-1429 (the checks, the memcpy
   call, the resume after it, the run to the ret, the post); the buffer is here the NEW block, a temporary block of the
   journal (in the blocks after the call, not in the entry's: awr_byte's in_tmp_block arm), where the fast arm's was
   the old one under wbuf_fp. Everything about the memory after the call is a premise (the composition reads it off
   fuzz_realloc's post and the callee journal); the journal count k is any K at or above the callee's kc. *)
Lemma pgt_granted : forall kc ly2 S2 U2 W2 regs2 mem2 md2 res K,
  ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ pgt_xs E' res (Z.of_nat (length text)) c (res + Z.of_nat (length text) + n)
    buf cap))
    pgt_ss1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs))) ->
  aregs_preserved (ms_regs ms') regs2 ->
  getr regs2 10%bv = w64 res -> 4096 + HEAD <= res ->
  fs_rblock tfibsegs B ly2 S2 W2 mem2 res c -> ~ In (res - HEAD, c + HEAD) (ablocks B ly S) -> fs_heads B ly2 S2 U2 ->
  zbytes_at tfibsegs W2 mem2 res text ->
  (forall a, spZ regs <= a < 2 ^ 64 ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  zbytes_at tfibsegs W2 mem2 s bs ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF s n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) s n) -> amem_range s n ->
  (forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)) ->
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) ->
  fs_glob tfibsegs W2 mem2 (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail ->
  (exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> kc <= K ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 542080) mem2 (seg_rom tfibsegs)) md2)
    (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md K U2
      (fun ly' S' W' regs' mem' md' =>
         ly' = ly2 /\ S' = S2 /\
         wout_ok B tfibsegs ly' S' W' mem' o res c 0 (text ++ bs) /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         fs_glob tfibsegs W' mem' (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail /\
         (forall i, 0 <= i < n ->
            mbyte tfibsegs (mrestrict (w_H W') mem') (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))).
Proof.
intros kc ly2 S2 U2 W2 regs2 mem2 md2 res K HJ2 HARU2 HS1 HP R10 Hres HRB HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR
  SDISJ SKEEP HGLOB2 Hcj HKK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
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
pose proof HRB as (Hin & Hb16 & Hc0 & Vhead).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (res - HEAD) (c + HEAD) (proj1 HARU2) Hin)
  as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & HbM).
assert (RQB : req_size (c + HEAD) = c + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (c + 16) 0); lia).
rewrite RQB in Hbceil, Hbapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hbapp. unfold HEAD in Hbceil, Hb4096.
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
unfold WMAX in HWM, HCAP, HcW.
assert (Ho47 : o + 32 <= 2 ^ 47) by lia.
assert (Hoc : alloc_ceiling + STK_put <= o) by lia.
(* the new buffer's bytes are no image byte *)
assert (BNI : forall t, res <= t < res + c -> ~ in_img tfibsegs t).
{ intros t Ht. apply (blk_img tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (res - HEAD) (c + HEAD) t (proj1 HARU2) Hin).
  rewrite RQB. unfold HEAD. lia. }
set (d := res + len) in *.
set (Er := Ereg regs2 (fs_extraT ++ pgt_xs E' res len c (d + n) buf cap)) in *.
(* the resume env's atoms *)
assert (P2 : getr regs2 2%bv = getr (ms_regs ms') 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms') 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms') 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms') 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms') 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18%bv = getr (ms_regs ms') 18%bv) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112)
  by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; exact R2).
assert (F3 : ew Er 3 = getr regs 3%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl), P3; exact R3).
assert (F4 : ew Er 4 = getr regs 4%bv) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl), P4; exact R4).
assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8; exact R8).
assert (F9 : ew Er 9 = Z_to_bv 64 n) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9; exact R9).
assert (F10 : ew Er 10 = Z_to_bv 64 res) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
assert (F18 : ew Er 18 = Z_to_bv 64 s) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18; exact R18).
assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
assert (F32u : bv_unsigned (ew Er 32) = SHADOW_OFF) by (rewrite F32; apply wz; unfold SHADOW_OFF; lia).
(* o's 32 bytes are addressable on any memory where AR holds over U2: the stack's shadow is 0 (as FSW_put.v:734-747) *)
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
assert (RAO : forall (m : word -> option byte) md', ARU tfibsegs B ly2 S2 U2 W2 m md' ->
  range_addressable (aview tfibsegs (w_H W2) m) SHADOW_OFF o 32).
{ intros m md' HARm.
  assert (HZS0 : zero_shadow (aview tfibsegs (w_H W2) (unpoison U2 m)) SHADOW_OFF
                  (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2)).
  { exact (al_zshadow _ _ LAWS ly2 S2 W2 (unpoison U2 m) md'
             (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) (proj1 HARm) (or_introl eq_refl)). }
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly2 S2 U2 W2 m md' (w_H W2) o 32 HARm ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W2) (unpoison U2 m)) SHADOW_OFF
               (ly_stk_lo ly2) (ly_stk_hi ly2 - ly_stk_lo ly2) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK1 : sh_ok tfibsegs fs_Bx pgt_SH1 Er (mrestrict (w_H W2) mem2)).
{ unfold pgt_SH1. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W2) mem2 Er fs_Bx 8%nat o 32 o 0 32 (RAO mem2 md2 HARU2)).
  - unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
  - apply (U_atom Er 8 o F8). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* `beqz a0` 0x84580: a0 = res <> 0 *)
srr_branch_tok fsw_put_tbl_ok HS1 SHOK1 fs_Bspan.
{ exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom Er 10 res F10) in Hc by lia.
  assert (U0 : YP0e.U Er (SLit 0) = 0) by reflexivity. rewrite U0 in Hc. apply Z.eqb_eq in Hc. lia. }
try clear Hc.
(* res + len, as the checks 0x845c0 / 0x845d0 and the copy read it, does not wrap (res + c <= alloc_ceiling, len < c) *)
assert (UD : YP0e.U Er (SAlu ALU_ADD (SOff 10 0) (SOff 34 0)) = d).
{ rewrite U_SAlu, (U_atom Er 10 res F10), (U_atom Er 34 len F34) by lia. cbn [zalu_raw].
  apply zcanon_id. unfold M64, d. lia. }
(* run 1: the checks of o (0x84588) and o + 16 (0x84594), the stores o->buf = a0 and o->cap = c, the reload of o + 8
   from frame slot 0, the checks of o (0x845a8) and o + 8 (0x845b0), to UBSan's pointer-overflow check 0x845c0 *)
fsw_aj_run_tokU fsw_put_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
{ lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
(* the run wrote only put's frame and o *)
assert (M0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
  ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
  vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
pose proof (fun a => apresent_grows _ _ _ a HG) as PR0.
clear HF HFr HG.
rename ms into msA.
(* 0x845c0 `bltu res + len, res`: the taken side is UBSan's trap 0x84680, refuted: res + len does not wrap *)
srr_branch_tok fsw_put_tbl_ok HS1 SHOK1 fs_Bspan.
{ exfalso. rewrite branch_ltu_U in Hc. rewrite UD, (U_atom Er 10 res F10) in Hc by lia.
  apply Z.ltb_lt in Hc. unfold d in Hc. lia. }
try clear Hc.
(* run 2: to UBSan's check 0x845d0 *)
fsw_aj_run_tokU fsw_put_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
{ lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (M0b : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
  ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. rewrite <- (M0 a Ha H1 H2). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
  vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR0 a Ha)) as PR0b.
clear M0 PR0 HF HFr HG.
rename ms into msB.
(* 0x845d0 `beqz (res <> 0) xor (res + len = 0)`: the taken side is UBSan's trap 0x84680, refuted: res <> 0 and
   res + len >= res > 0 *)
srr_branch_tok fsw_put_tbl_ok HS1 SHOK1 fs_Bspan.
{ exfalso. rewrite branch_eq_U in Hc.
  assert (UX : YP0e.U Er (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 10 0))
                 (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 34 0)) (SLit 1))) = 1).
  { rewrite (U_SAlu Er ALU_XOR), !(U_SAlu Er ALU_SLTU), UD, (U_atom Er 10 res F10), !U_SLit by lia. cbn [zalu_raw].
    change (zcanon 0) with 0. change (zcanon 1) with 1.
    destruct (Z.ltb_spec 0 res); [|lia]. destruct (Z.ltb_spec d 1); [unfold d in *; lia|]. reflexivity. }
  rewrite UX, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
try clear Hc.
(* run 3: to the call of __asan_memcpy (PC_memcpy 0x51d90, ra = 0x845e0) *)
fsw_aj_run_tokU fsw_put_tbl_ok HS1 HJ2 HARU2 SHOK1 fs_Bspan.
{ lazymatch goal with |- context C [ss_mem ?ssx] =>
    let rs' := eval vm_compute in (ss_mem ssx) in
    let g := context C [rs'] in change g end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
    [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
    [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
  (* the three runs wrote only put's frame and o *)
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha H1 H2. rewrite <- (M0b a Ha H1 H2). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u in Hr; lia. }
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o <= a < o + 32) ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
    by (intros a H0 H1 H2; unfold mbyte, mrestrict; rewrite (M1 a H0 H1 H2); reflexivity).
  pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR0b a Ha)) as PR1.
  clear M0b PR0b HF HFr HG.
  (* ---- the call of __asan_memcpy: its registers ---- *)
  assert (Ems0 : ms = mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (seg_rom tfibsegs))
    by exact (st_ok_restrict_mkst tfibsegs (w_H W2) Er _ ms HS1 eq_refl).
  assert (RT1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 542176) by (pf_reg HS1; reflexivity).
  assert (RT2 : spZ (ms_regs ms) = spZ regs - 112) by (unfold spZ at 1; pf_reg HS1; rewrite fsw_SOff0; exact F2).
  assert (RT3 : getr (ms_regs ms) 3%bv = getr regs 3%bv) by (pf_reg HS1; rewrite fsw_SOff0; exact F3).
  assert (RT4 : getr (ms_regs ms) 4%bv = getr regs 4%bv) by (pf_reg HS1; rewrite fsw_SOff0; exact F4).
  assert (RT8 : getr (ms_regs ms) 8%bv = Z_to_bv 64 o) by (pf_reg HS1; rewrite fsw_SOff0; exact F8).
  assert (RT9 : getr (ms_regs ms) 9%bv = Z_to_bv 64 n) by (pf_reg HS1; rewrite fsw_SOff0; exact F9).
  assert (RT10 : getr (ms_regs ms) 10%bv = w64 d).
  { pf_reg HS1. rewrite denot_lit_U. unfold w64. f_equal.
    rewrite U_SAlu, (U_atom Er 10 res F10), (U_atom Er 34 len F34) by lia. cbn [zalu_raw].
    apply zcanon_id. unfold M64, d. lia. }
  assert (RT11 : getr (ms_regs ms) 11%bv = w64 s) by (pf_reg HS1; rewrite fsw_SOff0; exact F18).
  assert (RT12 : getr (ms_regs ms) 12%bv = w64 n) by (pf_reg HS1; rewrite fsw_SOff0; exact F9).
  assert (RT23 : getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF) by (pf_reg HS1; rewrite fsw_SOff0; exact F32).
  (* s8 / s11: the shadow addresses of o + 8 and o over atom 8, as pgt_ss1 re-seated them (re-seated again at the
     resume, as FSW_put.v:915-919 / 1193-1217) *)
  assert (RT24 : getr (ms_regs ms) 24%bv = sv_denot Er (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 32 0)))
    by (pf_reg HS1; reflexivity).
  assert (RT27 : getr (ms_regs ms) 27%bv = sv_denot Er (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 32 0)))
    by (pf_reg HS1; reflexivity).
  (* the frame's words and o's fields at the call, read off the state *)
  pose proof (st_ok_mem_ok tfibsegs Er _ _ HS1) as (_ & HRS1 & _).
  cbn [ms_mem restrict ss_mem] in HRS1.
  pose proof (Forall_inv HRS1) as RF1.
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRS1. rename HRS1 into RO1.
  destruct RF1 as (_ & _ & _ & HCF). cbn [YP09.r_base YP09.r_chunks base_val] in HCF.
  rewrite F2 in HCF. rewrite Forall_forall in HCF.
  destruct RO1 as (_ & _ & _ & HCO1). cbn [YP09.r_base YP09.r_chunks base_val] in HCO1.
  rewrite F8u in HCO1. rewrite Forall_forall in HCO1.
  (* the call's premises *)
  assert (LOWT : forall t, 0 <= t < alloc_ceiling -> ms_mem ms (Z_to_bv 64 t) = mem2 (Z_to_bv 64 t))
    by (intros t Ht; apply M1; lia).
  assert (AVT : forall t, 0 <= t < alloc_ceiling ->
    aview tfibsegs (w_H W2) (ms_mem ms) t = aview tfibsegs (w_H W2) mem2 t)
    by (intros t Ht; apply (aview_at tfibsegs); exact (LOWT t Ht)).
  lazymatch type of HARU2 with ARU _ _ _ _ _ _ _ ?mdT =>
    assert (HPREc : ecall_preU tfibsegs B ly2 S2 U2 W2 (ms_regs ms) (ms_mem ms) mdT) end.
  { eapply (fsw_ecall_preU_at B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) (spZ regs - 112 - ot) HJ2 HARU2).
    - rewrite RT2. lia.
    - lia.
    - lia.
    - unfold ESTACK. lia.
    - unfold YK0s.ret_ok. rewrite RT1. apply bv_eq. vm_compute. reflexivity.
    - rewrite RT3. exact Hgp.
    - rewrite RT4. exact Htp. }
  assert (HDEST : dest_ok tfibsegs B ly2 S2 W2 (ms_regs ms) (ms_mem ms) d n).
  { intros a Ha.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD) (proj1 HARU2) Hin)
      as (_ & _ & _ & _ & Hbp & _).
    destruct (Hbp a ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as (Hpa & Hno).
    split; [|split; [exact Hno | rewrite RT2; unfold ESTACK, d in *; lia]].
    apply (apresent_writable tfibsegs). destruct Hpa as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite <- (fsw_pf_unp B ly2 S2 U2 W2 (ms_mem ms) _ a HARU2);
      [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
  assert (HAMRd : amem_range d n) by (unfold amem_range, d in *; lia).
  assert (HRAd : range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF d n).
  { apply (fsw_pf_ra_raw (w_H W2) U2 (ms_mem ms) d n); [unfold d in *; lia | unfold d in *; lia | |].
    - intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [unfold d in *; lia|].
      exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 (ms_mem ms)) _ res c x (proj1 HARU2) FH2 Hin Hc0
               ltac:(unfold d in *; lia)).
    - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD)
        d n (proj1 HARU2) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
  assert (HHULLd : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem ms)) d n).
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 (ms_mem ms) d n (proj2 (proj2 HARU2)));
      [unfold d in *; lia | unfold d in *; lia |].
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 (ms_mem ms)) _ (res - HEAD) (c + HEAD) d n
      (proj1 HARU2) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
  assert (HCPY : 0 <= s /\ s + n <= 2 ^ 63 /\ src_ok tfibsegs W2 (ms_regs ms) (ms_mem ms) s n /\
    (d + n <= s \/ s + n <= d) /\ amem_range s n /\
    range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF s n /\
    (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem ms)) s n)).
  { split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite RT2; unfold ESTACK; lia].
      rewrite AVT by lia. unfold zbytes_at in HZS2.
      destruct (HZS2 (Z.to_nat (a - s)) ltac:(lia)) as (Hv & _). specialize (Hv 0%nat ltac:(lia)).
      replace (s + Z.of_nat (Z.to_nat (a - s)) + Z.of_nat 0) with a in Hv by lia.
      unfold aview. rewrite Hv. discriminate. }
    split.
    { destruct (Z_le_gt_dec (d + n) s); [left; lia|]. destruct (Z_le_gt_dec (s + n) d); [right; lia|].
      exfalso. apply (SDISJ (Z.max s d)); unfold d, HEAD in *; lia. }
    split; [exact SAMR|]. split.
    { eapply range_addressable_agree; [|exact SRA2]. intros x Hx. apply AVT. unfold shadow_of_addr, SHADOW_OFF. lia. }
    intros Hn1 t Ht. rewrite AVT; [exact (SHULL2 Hn1 t Ht)|]. unfold shadow_addr, SHADOW_OFF in Ht. lia. }
  (* the call: __asan_memcpy (d, s, n) by its contract, the journal put back on the memory after it; the copy's
     window is a byte of the NEW block, a temporary block of the journal (in_tmp_block) *)
  rewrite Ems0.
  eapply SRr_bind.
  { apply (fsw_intrin_atU B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
      ly2 S2 U2 W2 (ms_mem ms) _ kc U2
      (fun a => d <= a < d + n \/ spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)) (w64 (raZ (ms_regs ms))) _
      (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
         (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem' (d + i) = aview tfibsegs (w_H W2) (ms_mem ms) (s + i)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)) ->
            aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) (ms_mem ms) a) /\
         (forall a, apresent (w_H W2) (ms_mem ms) a -> apresent (w_H W2) mem' a)) HJ2).
    - eapply SRr_mono.
      { exact (RT_memcpy ly2 S2 U2 W2 (ms_regs ms) (ms_mem ms) _ d s n HPREc RT10 RT11 RT12
          ltac:(unfold d in *; lia) ltac:(unfold d in *; lia) ltac:(unfold d in *; lia) HDEST HAMRd HRAd HHULLd HCPY). }
      cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & H10 & Hcp & Hfr & Hpr).
      split; [reflexivity|]. exists regs', mem', md'.
      split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|].
      split.
      { intros a Ha HnW.
        destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
        - apply (aview_unpoison_in tfibsegs). exact EU.
        - rewrite !(aview_unpoison_out tfibsegs) by exact EU.
          apply Hfr; [exact Ha | intros Hx; apply HnW; left; exact Hx | intros Hx; apply HnW; right; exact Hx]. }
      split.
      { intros a (Hh & b & Hb). split; [exact Hh|].
        destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
        - exists (Z_to_bv 8 0). apply unpoison_in. exact EU.
        - rewrite (unpoison_out U2 mem' (Z_to_bv 64 a) EU).
          rewrite (unpoison_out U2 (ms_mem ms) (Z_to_bv 64 a) EU) in Hb.
          destruct (Hpr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
      split; [exact HP'|]. split; [exact Hcp|]. split; [exact Hfr | exact Hpr].
    - intros a [Ha | Ha].
      + left. right. right. left. exists (res - HEAD), (c + HEAD). split; [exact Hin|]. split; [exact HNEW|].
        rewrite RQB. unfold d, HEAD in *. lia.
      + left. left. rewrite RT2 in Ha. unfold ESTACK in Ha. lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU3 & HP3 & HCP & HFR & HPR).
  (* ---- the resume at 0x845e0: FSW_put.fsw_pf_ssr with buf := res, cap := c ---- *)
  assert (ERA : w64 (raZ (ms_regs ms)) = Z_to_bv 64 542176) by (unfold w64, raZ; rewrite RT1, wz; [reflexivity | lia]).
  rewrite ERA.
  assert (S2' : getr regs3 2%bv = getr (ms_regs ms) 2%bv) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
  assert (S3' : getr regs3 3%bv = getr (ms_regs ms) 3%bv) by exact (HP3 3 ltac:(unfold acallee_saved; lia)).
  assert (S4' : getr regs3 4%bv = getr (ms_regs ms) 4%bv) by exact (HP3 4 ltac:(unfold acallee_saved; lia)).
  assert (S8' : getr regs3 8%bv = getr (ms_regs ms) 8%bv) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
  assert (S9' : getr regs3 9%bv = getr (ms_regs ms) 9%bv) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
  assert (S23' : getr regs3 23%bv = getr (ms_regs ms) 23%bv) by exact (HP3 23 ltac:(unfold acallee_saved; lia)).
  assert (S24' : getr regs3 24%bv = getr (ms_regs ms) 24%bv) by exact (HP3 24 ltac:(unfold acallee_saved; lia)).
  assert (S27' : getr regs3 27%bv = getr (ms_regs ms) 27%bv) by exact (HP3 27 ltac:(unfold acallee_saved; lia)).
  (* the bytes the copy kept *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - 112 - ESTACK <= a < spZ regs - 112) ->
    mbyte tfibsegs (mrestrict (w_H W2) mem3) a = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) a).
  { intros a Ha H1 H2. apply (mbyte_of_aview tfibsegs). apply HFR; [exact Ha | exact H1 | rewrite RT2; exact H2]. }
  assert (PR3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) by (intros a Ha; exact (HPR a (PR1 a Ha))).
  set (Er3 := Ereg regs3 (fs_extraT ++ pgt_xs E' res len c (d + n) buf cap)).
  assert (G2 : bv_unsigned (ew Er3 2) = spZ regs - 112)
    by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), S2'; exact RT2).
  assert (G8 : ew Er3 8 = Z_to_bv 64 o) by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), S8'; exact RT8).
  assert (G9 : ew Er3 9 = Z_to_bv 64 n) by (unfold Er3; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), S9'; exact RT9).
  assert (G32 : ew Er3 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold Er3; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G33 : ew Er3 33 = Z_to_bv 64 res) by (unfold Er3; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G34 : ew Er3 34 = Z_to_bv 64 len) by (unfold Er3; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G35 : ew Er3 35 = Z_to_bv 64 c) by (unfold Er3; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G36 : ew Er3 36 = Z_to_bv 64 (d + n))
    by (unfold Er3; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (G8u : bv_unsigned (ew Er3 8) = o) by (rewrite G8; apply wz; lia).
  assert (G9u : bv_unsigned (ew Er3 9) = n) by (rewrite G9; apply wz; lia).
  assert (G32u : bv_unsigned (ew Er3 32) = SHADOW_OFF) by (rewrite G32; apply wz; unfold SHADOW_OFF; lia).
  assert (G33u : bv_unsigned (ew Er3 33) = res) by (rewrite G33; apply wz; lia).
  assert (G34u : bv_unsigned (ew Er3 34) = len) by (rewrite G34; apply wz; lia).
  assert (G35u : bv_unsigned (ew Er3 35) = c) by (rewrite G35; apply wz; lia).
  assert (G36u : bv_unsigned (ew Er3 36) = d + n) by (rewrite G36; apply wz; unfold d in *; lia).
  (* a frame word / an o field of the call's state is the resume state's chunk *)
  assert (CMf : forall o0 (j : nat), ew Er3 j = ew Er j ->
    YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) (ms_mem ms)) (spZ regs - 112) (YP09.mkChunk o0 (CVal 8 (SOff j 0))) ->
    0 <= o0 -> o0 + 8 <= 112 ->
    YP09.chunk_ok tfibsegs Er3 (mrestrict (w_H W2) mem3) (spZ regs - 112) (YP09.mkChunk o0 (CVal 8 (SOff j 0)))).
  { intros o0 j Hj Hck Ho1 Ho2.
    apply (fsw_pf_chunk_move Er Er3 _ _ (spZ regs - 112) (spZ regs - 112) o0 o0 8 (SOff j 0) (SOff j 0) Hck).
    - rewrite !fsw_SOff0. exact Hj.
    - lia.
    - intros i Hi. cbn [Z.of_N] in Hi. apply KC; [lia | unfold d in *; lia | unfold ESTACK; lia]. }
  assert (CMo : forall off (w : N) e e', sv_denot Er3 e' = sv_denot Er e ->
    YP09.chunk_ok tfibsegs Er (mrestrict (w_H W2) (ms_mem ms)) o (YP09.mkChunk off (CVal w e)) ->
    0 <= off -> off + Z.of_N w <= 32 ->
    YP09.chunk_ok tfibsegs Er3 (mrestrict (w_H W2) mem3) o (YP09.mkChunk off (CVal w e'))).
  { intros off w e e' He Hck Ho1 Ho2.
    apply (fsw_pf_chunk_move Er Er3 _ _ o o off off w e e' Hck He); [lia|].
    intros i Hi. apply KC; [lia | unfold d in *; lia | unfold ESTACK; lia]. }
  (* the shadow-base cells on the memory after the copy (as FSW_put.v:985-1003) *)
  destruct (fsw_got_shadow B ly2 S2 W2 (unpoison U2 mem3) md3 (proj1 HSS) (proj2 HSS) (proj1 HARU3)) as [Kgot Kcell].
  assert (MBL : forall x, 0 <= x < SHADOW_OFF ->
    mbyte tfibsegs (mrestrict (w_H W2) mem3) x = mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem3)) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (ARU_mem_low tfibsegs B ly2 S2 U2 W2 mem3 md3 (Z_to_bv 64 x) HARU3
      ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
    reflexivity. }
  assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
    val_mem tfibsegs (mrestrict (w_H W2) (unpoison U2 mem3)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a 8 v).
  { intros a v Ha Hb Hv k0 Hk0. rewrite (MBL (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
  assert (Vgot : val_mem tfibsegs (mrestrict (w_H W2) mem3) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
    tfib_D_asan_shadow_memory_dynamic_address).
  { apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
    | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
    | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem3) _ _ Kgot)]. }
  assert (Vcell : val_mem tfibsegs (mrestrict (w_H W2) mem3) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
  { apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
    | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
    | exact (val_mem_of_rdword tfibsegs (w_H W2) (unpoison U2 mem3) _ _ Kcell)]. }
  (* the end of the new text is a byte of the new block: present after the copy *)
  assert (PZ : apresent (w_H W2) mem3 (d + n)).
  { destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem3) md3 (res - HEAD) (c + HEAD) (proj1 HARU3) Hin)
      as (_ & _ & _ & _ & Hbp & _).
    destruct (Hbp (d + n) ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as ((Hh & b & Hb) & _).
    split; [exact Hh|]. exists b.
    rewrite <- (fsw_pf_unp B ly2 S2 U2 W2 mem3 md3 (d + n) HARU3);
      [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  (* the end of the new text is a buffer byte, so no image byte: off the two shadow-base cells *)
  assert (ZG : d + n + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/
               tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= d + n).
  { destruct (Z_le_gt_dec (d + n + 1) tfib_D_GOT_asan_shadow_memory_dynamic_address); [left; lia|].
    destruct (Z_le_gt_dec (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
    exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address in *; lia. }
  assert (ZC : d + n + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/
               tfib_D_asan_shadow_memory_dynamic_address + 8 <= d + n).
  { destruct (Z_le_gt_dec (d + n + 1) tfib_D_asan_shadow_memory_dynamic_address); [left; lia|].
    destruct (Z_le_gt_dec (tfib_D_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
    exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
    unfold tfib_D_asan_shadow_memory_dynamic_address in *; lia. }
  assert (HSR0 : st_ok tfibsegs Er3
      (mkSS 542176 sr_atoms (fsT_ret_regions 112 fsw_pf_cs [fsw_pf_o2; fsw_pf_z2]) None
        (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: fsw_pf_gf2) []
           fsw_pf_al2))
      (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); fold Er3.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - unfold fsT_ret_regions. cbn [app].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      + (* the frame, its 13 saved words *)
        unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G2. split; [lia|]. split; [lia|]. split.
        * intros q Hq. apply (apresent_writable tfibsegs).
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem3 md3 _ HARU3); [lia|]. apply Hpres3. lia.
        * unfold fsw_pf_cs. repeat constructor.
          all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o2 (CVal 8 (SOff ?j 0))) =>
            exact (CMf o2 j eq_refl (HCF (YP09.mkChunk o2 (CVal 8 (SOff j 0)))
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
          [rewrite fsw_SOff0, G32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
      + (* o: buf = res, len, cap = c, failed = 0, as run 1 stored them; its length field writable *)
        unfold fsw_pf_o2, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G8u. split; [lia|]. split; [lia|]. split.
        { intros q Hq. apply (apresent_writable tfibsegs).
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem3 md3 _ HARU3); [lia|]. apply Hpres3. lia. }
        constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
        * exact (CMo 0 8%N (SOff 10 0) (SOff 33 0) ltac:(rewrite !fsw_SOff0, G33, F10; reflexivity)
                   (HCO1 (YP09.mkChunk 0 (CVal 8 (SOff 10 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 8 8%N (SOff 34 0) (SOff 34 0) ltac:(rewrite !fsw_SOff0, G34, F34; reflexivity)
                   (HCO1 (YP09.mkChunk 8 (CVal 8 (SOff 34 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 16 8%N (SOff 35 0) (SOff 35 0) ltac:(reflexivity)
                   (HCO1 (YP09.mkChunk 16 (CVal 8 (SOff 35 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
        * exact (CMo 24 4%N (SLit 0) (SLit 0) ltac:(reflexivity)
                   (HCO1 (YP09.mkChunk 24 (CVal 4 (SLit 0))) ltac:(repeat (first [left; reflexivity | right])))
                   ltac:(lia) ltac:(cbn [Z.of_N]; lia)).
      + (* the byte after the new text, writable *)
        unfold fsw_pf_z2, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite G36u. split; [unfold d in *; lia|]. split; [unfold d in *; lia|]. split; [|constructor].
        intros q Hq. replace (d + n + q) with (d + n) by lia. apply (apresent_writable tfibsegs). exact PZ.
    - apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, fsw_pf_o2, fsw_pf_z2, extent_of_region.
      cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite G2, G8u, G36u.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      unfold d in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok fsw_pf_gf2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite G2, G32u, G8u, G33u, G34u, G35u, G9u, G36u. unfold fsw_pf_CEIL.
        change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold d in *. repeat split; lia.
      + cbn [f_alias alias_ok fsw_pf_al2]. split; [|exact I].
        apply U_inj. rewrite !U_SAlu, (U_atom Er3 9 n G9), (U_atom Er3 33 res G33), (U_atom Er3 34 len G34),
          (U_atom Er3 36 (d + n) G36) by (unfold d in *; lia).
        cbn [zalu_raw]. rewrite (zcanon_id (n + res)) by (unfold M64; lia).
        rewrite zcanon_id by (unfold M64; lia). unfold d. lia. }
  (* the resume state's three re-seated registers: s7 the shadow base, s8 / s11 the shadow addresses of o + 8 and o
     over the resumed o (atom 8), which the token engine reads at 0x845e0 / 0x845f4 (FSW_put.v:1193-1217) *)
  assert (HSR1 : st_ok tfibsegs Er3 (fsw_pf_ssk fsw_pf_rs1)
                   (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))).
  { refine (st_ok_set_reg tfibsegs Er3 _ _ 23%bv (SOff 32 0) HSR0 _ _).
    - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    - change (ms_regs (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))) with regs3.
      rewrite fsw_SOff0, G32, S23'. exact RT23. }
  assert (HSR2 : st_ok tfibsegs Er3 (fsw_pf_ssk fsw_pf_rs2)
                   (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))).
  { refine (st_ok_set_reg tfibsegs Er3 _ _ 24%bv fsw_pf_s8 HSR1 _ _).
    - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    - change (ms_regs (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))) with regs3.
      rewrite S24', RT24. apply bv_eq.
      change (YP0e.U Er (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 32 0)) = YP0e.U Er3 fsw_pf_s8).
      unfold fsw_pf_s8. rewrite !U_SAlu, !U_SOff, !U_SLit, F8u, G8u, F32u, G32u. reflexivity. }
  assert (HSR : st_ok tfibsegs Er3 fsw_pf_ssr
                  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))).
  { refine (st_ok_set_reg tfibsegs Er3 _ _ 27%bv fsw_pf_s11 HSR2 _ _).
    - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    - change (ms_regs (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 542176) mem3 (seg_rom tfibsegs)))) with regs3.
      rewrite S27', RT27. apply bv_eq.
      change (YP0e.U Er (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 32 0)) = YP0e.U Er3 fsw_pf_s11).
      unfold fsw_pf_s11. rewrite !U_SAlu, !U_SOff, !U_SLit, F8u, G8u, F32u, G32u. reflexivity. }
  clear HSR0 HSR1 HSR2.
  assert (SHOK2 : sh_ok tfibsegs fs_Bx fsw_pf_SH2 Er3 (mrestrict (w_H W2) mem3)).
  { unfold fsw_pf_SH2. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range tfibsegs (w_H W2) mem3 Er3 fs_Bx 8%nat o 32 o 0 32 (RAO mem3 md3 HARU3)).
      + unfold fs_Bx. apply (U_atom Er3 32 SHADOW_OFF G32). unfold SHADOW_OFF; lia.
      + apply (U_atom Er3 8 o G8). lia.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF. lia.
    - assert (HRAz : range_addressable (aview tfibsegs (w_H W2) mem3) SHADOW_OFF (d + n) 1).
      { apply (fsw_pf_ra_raw (w_H W2) U2 mem3 (d + n) 1); [unfold d in *; lia | unfold d in *; lia | |].
        - intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU3))); [unfold d in *; lia|].
          exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 mem3) md3 res c x (proj1 HARU3) FH2 Hin Hc0
                   ltac:(unfold d in *; lia)).
        - apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem3) md3 (res - HEAD) (c + HEAD)
            (d + n) 1 (proj1 HARU3) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
      apply (shent_ok_of_range tfibsegs (w_H W2) mem3 Er3 fs_Bx 36%nat (d + n) 1 (d + n) 0 1 HRAz).
      + unfold fs_Bx. apply (U_atom Er3 32 SHADOW_OFF G32). unfold SHADOW_OFF; lia.
      + apply (U_atom Er3 36 (d + n) G36). unfold d in *; lia.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF, d in *. lia. }
  (* run 4 (the fast arm's, FSW_put.v:1239): the checks of o + 8 (0x845e4) and o (0x845f8) through the re-seated
     s8 / s11, the length store o + 8, to UBSan's pointer-overflow check of res + len + n, 0x84604 *)
  fsw_aj_run_tokU fsw_put_tbl_ok HSR HJ3 HARU3 SHOK2 fs_Bspan.
  { lazymatch goal with |- context C [ss_mem ?ssx] =>
      let rs' := eval vm_compute in (ss_mem ssx) in
      let g := context C [rs'] in change g end.
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
      [reflexivity | rewrite G2; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
      [reflexivity | rewrite G8u; lia | cbn; lia | cbn; lia |].
    eapply awr_ok_cons_gen with (k := 36%nat) (b := d + n); [reflexivity | exact G36u | | apply awr_ok_nil].
    intros a Ha. cbn in Ha. left. right. right. left.
    exists (res - HEAD), (c + HEAD). split; [exact Hin|]. split; [exact HNEW|]. rewrite RQB. unfold d, HEAD in *. lia. }
  lazymatch type of HSR with st_ok _ _ _ (restrict _ ?m) => rename m into msD end.
  (* run 4 wrote only the frame, o's length field and the 0 after the new text (in fact only the field) *)
  assert (MD : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
    a <> d + n -> ms_mem msD (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
  { intros a Ha H1 H2 H3. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?G2, ?G8u, ?G36u in Hr; lia. }
  pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR3 a Ha)) as PRD.
  clear HF HFr HG.
  (* 0x84604 `bltu d + n, res`: the taken side is UBSan's trap 0x84680, refuted: d + n = res + len + n >= res *)
  srr_branch_tok fsw_put_tbl_ok HSR SHOK2 fs_Bspan.
  { exfalso. rewrite branch_ltu_U in Hc.
    rewrite (U_atom Er3 36 (d + n) G36), (U_atom Er3 33 res G33) in Hc by (unfold d in *; lia).
    apply Z.ltb_lt in Hc. unfold d in *. lia. }
  try clear Hc.
  (* run 5 (FSW_put.v:1271): the checks 0x84614 / 0x84618, the shadow check of d + n (0x84628 into the
     partial-granule slow block 0x84698, compare 0x8469c), the 0 after the new text, the epilogue, to the ret 0x84668 *)
  fsw_aj_run_tokU fsw_put_tbl_ok HSR HJ3 HARU3 SHOK2 fs_Bspan.
  { lazymatch goal with |- context C [ss_mem ?ssx] =>
      let rs' := eval vm_compute in (ss_mem ssx) in
      let g := context C [rs'] in change g end.
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
      [reflexivity | rewrite G2; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
      [reflexivity | rewrite G8u; lia | cbn; lia | cbn; lia |].
    eapply awr_ok_cons_gen with (k := 36%nat) (b := d + n); [reflexivity | exact G36u | | apply awr_ok_nil].
    intros a Ha. cbn in Ha. left. right. right. left.
    exists (res - HEAD), (c + HEAD). split; [exact Hin|]. split; [exact HNEW|]. rewrite RQB. unfold d, HEAD in *. lia. }
  lazymatch type of HSR with st_ok _ _ _ (restrict _ ?m) => rename m into msf end.
    (* the two runs wrote only the frame, o's length field and the 0 after the new text *)
    assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
      a <> d + n -> ms_mem msf (Z_to_bv 64 a) = mem3 (Z_to_bv 64 a)).
    { intros a Ha H1 H2 H3. rewrite <- (MD a Ha H1 H2 H3). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
      vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?G2, ?G8u, ?G36u in Hr; lia. }
    pose proof (fun a Ha => apresent_grows _ _ _ a HG (PRD a Ha)) as PRF.
    clear MD PRD.
    lazymatch type of HSR with st_ok _ ?Ef _ _ => assert (HAG : env_agree 50 Er3 Ef) end.
    { lazymatch goal with |- env_agree _ _ (ewset (ewset _ _ ?w1) _ ?w2) => exact (env_agree_extK Er3 50 [w1; w2]) end. }
    assert (FR1 : getr (ms_regs msf) 1%bv = getr regs 1%bv).
    { pf_reg HSR. rewrite (sv_denot_agree 50 Er3 _ (SOff 37 0) HAG eq_refl). rewrite fsw_SOff0.
      change (ew Er3 37) with (ew E' 1). apply pgt_E'_reg; [lia | reflexivity]. }
    (* o's fields and the 0 after the new text, read off the final state *)
    pose proof (st_ok_mem_ok tfibsegs _ _ _ HSR) as (_ & HRSF & _).
    cbn [ms_mem restrict ss_mem] in HRSF.
    apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HRSF.
    pose proof (Forall_inv HRSF) as RO. apply Forall_inv_tail, Forall_inv in HRSF. rename HRSF into RZ.
    destruct RO as (_ & _ & _ & HCO). cbn [YP09.r_base YP09.r_chunks base_val] in HCO.
    rewrite (proj1 HAG 8%nat ltac:(lia)), G8u in HCO.
    destruct RZ as (_ & _ & _ & HCZ). cbn [YP09.r_base YP09.r_chunks base_val] in HCZ.
    rewrite (proj1 HAG 36%nat ltac:(lia)), G36u in HCZ. apply Forall_inv in HCZ.
    assert (VLEN : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 8) 8 (len + n)).
    { apply (val_of_chunk_ok tfibsegs _ _ o 8 8 _ (len + n) (Forall_inv HCO)).
      - lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er3 => fail | _ =>
          rewrite (sv_denot_agree 50 Er3 Ef e HAG eq_refl) end end.
        rewrite denot_lit_U. f_equal.
        rewrite U_SAlu, (U_atom Er3 9 n G9), (U_atom Er3 34 len G34) by lia. cbn [zalu_raw].
        rewrite zcanon_id by (unfold M64; lia). lia.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    rewrite Forall_forall in HCO.
    assert (VBUF : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 0) 8 res).
    { apply (val_of_chunk_ok tfibsegs _ _ o 0 8 (SOff 33 0) res
        (HCO (YP09.mkChunk 0 (CVal 8 (SOff 33 0))) ltac:(repeat (first [left; reflexivity | right])))).
      - rewrite (sv_denot_agree 50 Er3 _ (SOff 33 0) HAG eq_refl), fsw_SOff0. exact G33.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    assert (VCAP : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 16) 8 c).
    { apply (val_of_chunk_ok tfibsegs _ _ o 16 8 (SOff 35 0) c
        (HCO (YP09.mkChunk 16 (CVal 8 (SOff 35 0))) ltac:(repeat (first [left; reflexivity | right])))).
      - rewrite (sv_denot_agree 50 Er3 _ (SOff 35 0) HAG eq_refl), fsw_SOff0. exact G35.
      - cbn [Z.of_N]. lia.
      - cbn [Z.of_N]. lia. }
    assert (VFAIL : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (o + 24) 4 0).
    { apply (val_of_chunk_ok tfibsegs _ _ o 24 4 (SLit 0) 0
        (HCO (YP09.mkChunk 24 (CVal 4 (SLit 0))) ltac:(repeat (first [left; reflexivity | right]))));
        [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
    assert (VZ : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (d + n + 0) 1 0).
    { apply (val_of_chunk_ok tfibsegs _ _ (d + n) 0 1 (SLit 0) 0 HCZ); [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
    (* every other byte: kept, against the memory after fuzz_realloc and against put's entry *)
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
      a <> d + n -> mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W2) mem3) a)
      by (intros a H0 H1 H2 H3; unfold mbyte, mrestrict; rewrite (MF a H0 H1 H2 H3); reflexivity).
    assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
      mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
    { intros a Ha Ho. rewrite (KF a) by (unfold d in *; lia). rewrite (KC a) by (unfold ESTACK, d in *; lia).
      rewrite (K1 a) by lia. exact (KEEPE a Ha). }
    assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (d <= a < d + n + 1) ->
      mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a).
    { intros a Ha Hd. rewrite (KF a) by (unfold d in *; lia). rewrite (KC a) by (unfold ESTACK, d in *; lia).
      apply K1; lia. }
    assert (VL2 : forall a k v, 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
      (forall i, 0 <= i < Z.of_nat k -> ~ (d <= a + i < d + n + 1)) ->
      val_mem tfibsegs (mrestrict (w_H W2) mem2) a k v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) a k v).
    { intros a k v Ha Hk Ho Hv i Hi. rewrite (KL (a + Z.of_nat i) ltac:(lia) (Ho (Z.of_nat i) ltac:(lia))). exact (Hv i Hi). }
    (* the return *)
    eapply (fsw_retU B fsw_put_tbl fsw_put_tbl_ok).
    * exact HSR.
    * vm_compute; reflexivity.
    * vm_compute; reflexivity.
    * rewrite FR1. exact Hra.
    * eapply ajournal_mono_k; [exact HJ3 | exact HKK].
    * exact HARU3.
    * lazymatch type of HSR with
      | st_ok _ ?Ef ?ssf _ =>
        apply (fsw_preserved (w_H W2) Ef ssf _ regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HSR);
        [vm_compute; reflexivity|];
        let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [CALLEE_SAVED In] in Hr;
        repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
      end;
      cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er3 => fail | _ =>
        rewrite (sv_denot_agree 50 Er3 Ef e HAG eq_refl) end end;
      first
      [ rewrite denot_lit_U, U_SOff, G2, zcanon_id by (unfold M64; lia);
        replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
      | rewrite fsw_SOff0; unfold Er3; rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl), S3'; exact RT3
      | rewrite fsw_SOff0; unfold Er3; rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl), S4'; exact RT4
      | lazymatch goal with |- sv_denot _ (SOff ?j 0) = _ =>
          let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                       else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
          rewrite fsw_SOff0; change (ew Er3 j) with (ew E' k); apply pgt_E'_reg; [lia | vm_compute; reflexivity]
        end ].
    * intros matq.
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [lia|]. split.
        { intros i Hi.
          assert (Hp : apresent (w_H W2) mem2 (o + i)).
          { apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia. }
          pose proof (PRF _ Hp) as Hp'. split; [exact (apresent_writable tfibsegs _ _ _ Hp') | exact Hp']. }
        split; [lia|]. split; [lia|].
        split; [rewrite Z.add_0_r in VBUF; exact VBUF|].
        split; [rewrite length_app, Nat2Z.inj_add; fold len; rewrite Hlen; exact VLEN|].
        split; [exact VCAP|]. split; [exact VFAIL|].
        split; [left; reflexivity|].
        split; [unfold WriterSpec.bytes_ok in *; apply Forall_app; split; assumption|].
        right. split; [exact Hcj|]. split; [|split].
        - unfold fs_rblock. split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hc0|].
          apply (VL2 (res - HEAD) 8%nat c); [unfold HEAD; lia | unfold HEAD; lia
            | intros i Hi; unfold d, HEAD in *; lia | exact Vhead].
        - rewrite length_app, Nat2Z.inj_add. fold len. lia.
        - unfold zbytes_at in HTXT, HZS2 |- *. intros j Hjl. rewrite !length_app in Hjl. cbn [length] in Hjl.
          destruct (Nat.lt_ge_cases j (length text)) as [Hj1|Hj1].
          + rewrite <- app_assoc, app_nth1 by exact Hj1.
            destruct (HTXT j Hj1) as (Hv & Hr).
            split; [|exact Hr].
            apply (VL2 (res + Z.of_nat j) 1%nat); [lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold d, len in *; lia
              | intros i Hi; cbn [Z.of_nat Pos.of_succ_nat] in Hi; unfold d, len in *; lia | exact Hv].
          + destruct (Nat.lt_ge_cases j (length text + length bs)) as [Hj2|Hj2].
            * rewrite <- app_assoc, app_nth2 by exact Hj1. rewrite app_nth1 by lia.
              destruct (HZS2 (j - length text)%nat ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
              intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk). rewrite <- Hv.
              replace (res + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat (j - length text)) by (unfold d, len; lia).
              replace (s + Z.of_nat (j - length text) + Z.of_nat 0) with (s + Z.of_nat (j - length text)) by lia.
              rewrite (KF (d + Z.of_nat (j - length text))) by (unfold d, len in *; lia).
              rewrite (fsw_pf_mbyte_aview2 (w_H W2) (ms_mem ms) mem3 _ _ (HCP (Z.of_nat (j - length text)) ltac:(lia))).
              unfold mbyte, mrestrict. rewrite (LOWT (s + Z.of_nat (j - length text))) by lia. reflexivity.
            * assert (Ej : j = (length text + length bs)%nat) by lia. subst j.
              rewrite <- app_assoc, app_nth2 by lia. rewrite app_nth2 by lia.
              replace (length text + length bs - length text - length bs)%nat with 0%nat by lia. cbn [nth].
              split; [|lia].
              replace (res + Z.of_nat (length text + length bs)) with (d + n + 0) by (unfold d, len; lia). exact VZ. }
      split.
      { intros a Ha Hno. split; [apply KH; lia|].
        split; intros _.
        - apply (apresent_writable tfibsegs). apply PRF.
          apply (fsw_apresent_unpoison B ly2 S2 U2 W2 mem2 md2 _ HARU2m); [lia|]. apply Hpres2. lia.
        - apply (apresent_writable tfibsegs). apply HPRESENT. lia. }
      split.
      { assert (GI : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 ->
          val_mem tfibsegs (mrestrict (w_H W2) mem2) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) g 8 v).
        { intros g v Hg1 Hg2 Hv. apply VL2; [lia | lia | | exact Hv].
          intros i Hi Hx. apply (BNI (g + i)); [unfold d in *; lia|]. apply fsw_pf_in_img. lia. }
        unfold fs_glob, fs_glob_at in HGLOB2 |- *. destruct HGLOB2 as (GL1 & GL2 & GL3 & GL4 & GR).
        split; [apply GI; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact GL1]|].
        split; [apply GI; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact GL2]|].
        split; [apply GI; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact GL3]|].
        split; [apply GI; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact GL4]|].
        exact GR. }
      intros i Hi. rewrite <- (SKEEP i Hi). apply KL; [lia|]. intros Hx. apply (SDISJ (s + i)); [lia | unfold d, HEAD in *; lia].
Qed.


End pgt.
