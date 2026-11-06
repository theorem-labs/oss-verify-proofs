(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow_tail.v, with its module paths, module names and numbers changed; 18 of its 516 lines of code are new or changed and 1496 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm, the composition of the second half: pgt_run, from the call
   of fuzz_realloc (0x82bc4, ra = 0x84580) to put_spec's post (lib/B/FSW_put.v put_post), over fuzz_realloc_spec's
   three outcomes - refused (cnt = fail; FSW_put_grow_refused.v pgt_refused), granted from a NULL buffer (cap = 0, its
   p = 0 arm, journal 1; FSW_put_grow_granted.v pgt_granted) and granted from a live buffer (cap <> 0, its p <> 0 arm,
   journal 3; pgt_granted) - with the callee's pre and the resume (FSW_put_grow_call.v pgt_callee_pre / pgt_resume) and
   the source range after the call (FSW_put_grow_src.v pgt_src_after). The Section is lib/B/FSW_put_grow_tail.v's; the
   pieces' lemmas are re-stated over it (their files close their Sections) and applied as A applies them.

   TAKEN FROM: lib/A/FSW_put_grow_tail.v at a working branch 860b2fb1188 (the same blob is on
   a working branch f0e2574c33c): pgt_put1 (:1596-1604), pgt_bb (:1826-1835) and pgt_run (:1837-2156),
   unchanged in form (B's resume pc 542080).

   RULE-24: proves function put (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x8449c; the GROW arm)
   (reuse search: proof-index put_holds / put_close_grow / fsw_pg_loop / pgt_run / fsw_pg_entry_run, index v5
   built 2026-10-29T07:26:27Z, plus a git grep with a passing control (put_failed_run) of 599 cold lib/B trees: no
   lib/B/FSW_put_grow* or FSW_put_holds* anywhere; checker a Theorem Labs lane CONFIRM 09:2xZ). *)
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
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_put FSW_put_grow FSW_put_grow_model FSW_put_grow_tail
FSW_put_grow_call FSW_put_grow_granted FSW_put_grow_refused FSW_put_grow_src.
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

(* the pieces' lemmas, re-stated over this Section's data *)
Lemma pgt_callee_pre : exists ch1, fpreU tfibsegs B STK_fuzz_realloc ly S U W (ms_regs ms') (ms_mem ms') mdc ch1.
Proof. eapply FSW_put_grow_call.pgt_callee_pre; eassumption. Qed.
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
Proof. intros. eapply FSW_put_grow_call.pgt_resume; eassumption. Qed.
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
Proof. intros. eapply FSW_put_grow_granted.pgt_granted; eassumption. Qed.
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
Proof. intros. eapply FSW_put_grow_refused.pgt_refused; eassumption. Qed.
Lemma pgt_src_after : forall FP1 kc ly2 S2 U2 W2 mem2 md2,
  ajournal tfibsegs B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S W (unpoison U (ms_mem ms')) mdc []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 -> fs_heads B ly2 S2 U2 ->
  (forall a, inFP FP1 a -> inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap)) ->
  (forall p k, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> In (p, k) (ablocks B ly2 S2)) ->
  (forall r, In r U2 -> In r U \/ exists m, In (fst r, m) (ablocks B ly2 S2) /\ ~ In (fst r, m) (ablocks B ly S) /\
     snd r = HEAD /\ HEAD <= req_size m) ->
  zbytes_at tfibsegs W2 mem2 s bs /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) s n) /\ amem_range s n /\
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) /\
  (forall q m, In (q, m) (ablocks B ly2 S2) -> ~ In (q, m) (ablocks B ly S) -> 0 < m ->
     forall x, s <= x < s + n -> ~ (q <= x < q + req_size m)).
Proof. intros. eapply FSW_put_grow_src.pgt_src_after; eassumption. Qed.

(* ================= the composition ================= *)
(* put1 on the grow arm (WriterApp.v put1: failed = 0, need = len + n + 1 > cap, newcap cap need = c) *)
Lemma pgt_put1 : WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs =
  if cnt =? fail then WriterApp.mkW 1 text cap ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) [c]
  else WriterApp.mkW 0 (text ++ bs) c ((cnt + 1) mod 2 ^ 64) fail [c].
Proof.
unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls negb Z.eqb].
rewrite Hlen. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite <- Hcnew. reflexivity.
Qed.


(* blocks_bytes is the sum of the block sizes (as A/AD1r.v:608 blocks_bytes_ablocks, over Reusable's bsum) *)
Lemma pgt_bb : forall ly0 S0, blocks_bytes S0 = YCbq.bsum (ablocks B ly0 S0).
Proof.
intros ly0 S0.
assert (E : blocks_bytes S0 = fold_right (fun b acc => snd b + acc) 0 (blocks S0)).
{ unfold blocks_bytes, blocks. induction (st_chunks S0) as [|k ks IH]; cbn; [reflexivity|].
  destruct (is_alloc k); cbn; rewrite IH; reflexivity. }
rewrite E. clear E. unfold ablocks, YCbq.bsum.
induction (blocks S0) as [|b l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(* ---- THE TOP LEMMA: from the call of fuzz_realloc to put_spec's post. fuzz_realloc_spec's three outcomes: refused
   (cnt = fail; pgt_refused), granted from a NULL buffer (cap = 0, its p = 0 arm, journal 1; pgt_granted) and granted
   from a live buffer (cap <> 0, its p <> 0 arm, journal 3; pgt_granted). put_spec's count wevk cap st' is 1 at
   cap = 0 and 3 at cap <> 0 (pgt_put1), at or above each arm's journal (ajournal's k only rises). ---- *)
Lemma pgt_run :
  SRr tfibsegs W (mkCfg ms' mdc)
    (put_post B ly S U W regs mem md ot o s n buf cap 0 text bs live peak cnt fail).
Proof.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & _).
pose proof HSRC as (Hs0 & Hsn).
pose proof HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
pose proof HGLOB as (G1 & G2 & G3 & G4 & Hlp & Hpk & Hcnt0 & Hfl).
assert (HARU0 : ARU tfibsegs B ly S U W mem md) by exact (fsw_ARU B STK_put ly S U W regs mem md ch HPREU).
destruct pgt_callee_pre as (ch1 & HPREc).
destruct pgt_call_regs as (Ems & R1 & R2 & _ & _ & _ & _ & R10 & R11 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
assert (Hcls : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
  by (destruct Hcase as [(E & _) | (Hj & _)]; [left; exact E | right; exact Hj]).
assert (Hcj : exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j)
  by (rewrite Hcnew; exact (proj1 (put_grow_newcap_class cap _ Hcls HCAP HWM))).
unfold WMAX in HWM, HCAP, HcW.
assert (Hn0 : 0 <= n) by lia.
assert (Hlen0 : 0 <= Z.of_nat (length text)) by lia.
assert (Bc : bsz c = c + HEAD) by (unfold bsz; rewrite (proj2 (Z.eqb_neq c 0)) by lia; reflexivity).
assert (RQc : req_size (c + HEAD) = c + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (c + 16) 0); lia).
(* ---- the model: put1's two outcomes, its journal count and its budget ---- *)
pose proof pgt_put1 as HPUT.
assert (HWV : wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = if cap =? 0 then 1 else 3).
{ rewrite HPUT. unfold wevk, wev0, wcalls. destruct (cnt =? fail); cbn [WriterApp.w_calls length Z.of_nat];
  destruct (cap =? 0); reflexivity. }
assert (HWC : wcalls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = 1)
  by (rewrite HPUT; unfold wcalls; destruct (cnt =? fail); reflexivity).
pose proof HBUD as (Bev & Bbb & Blv & Bcn). rewrite HWV in Bev. rewrite HWC in Bcn.
assert (Bev0 : cap = 0 -> st_nev S + 1 <= EV_MAX)
  by (intros E; rewrite (proj2 (Z.eqb_eq _ _) E) in Bev; exact Bev).
assert (Bev3 : cap <> 0 -> st_nev S + 3 <= EV_MAX)
  by (intros E; rewrite (proj2 (Z.eqb_neq _ _) E) in Bev; exact Bev).
assert (HCG : cnt <> fail -> WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = c).
{ intros Hne. rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hne). reflexivity. }
(* ---- the buffer: none (cap = 0), or a live reader block whose head is in U ---- *)
assert (HCZ : cap = 0 -> buf = 0 /\ text = []).
{ intros E. destruct Hcase as [(_ & Hb & Ht) | ((j & Hj & Hcj') & _)]; [split; assumption|].
  exfalso. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
assert (HCN : cap <> 0 -> (exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly S W mem buf cap /\
  Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W mem buf (text ++ [0])).
{ intros E. destruct Hcase as [(Hc & _) | Hx]; [contradiction | exact Hx]. }
assert (HCB : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S) /\ 4096 + HEAD <= buf /\ 0 < cap /\
  buf + cap <= alloc_ceiling /\ in_app (buf - HEAD) (cap + HEAD)).
{ intros E. destruct (HCN E) as (_ & (Hin & _ & Hcp & _) & _).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
    as (_ & Hb4096 & Hbc & Happ & _).
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  rewrite RQ in Hbc, Happ.
  split; [exact Hin|]. split; [unfold HEAD in *; lia|]. split; [exact Hcp|]. split; [unfold HEAD in *; lia | exact Happ]. }
(* the old buffer's cap bytes, every one present (a live block's bytes are), as a list *)
set (old := pgt_bytes (mrestrict (w_H W) (ms_mem ms')) buf (Z.to_nat cap)).
assert (HOLD : cap <> 0 -> length old = Z.to_nat cap /\ zbytes_at tfibsegs W (ms_mem ms') buf old).
{ intros E. destruct (HCB E) as (Hin & Hb & Hcp & Hbc & Hbs).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin) as (_ & _ & _ & _ & Hbp & _).
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  unfold zbytes_at. apply pgt_bytes_ok. intros j Hj.
  assert (Hj' : Z.of_nat j < cap) by (apply Nat2Z.inj_lt in Hj; rewrite Z2Nat.id in Hj by lia; exact Hj).
  apply pgt_mbyte_present. apply HPRK.
  destruct (Hbp (buf + Z.of_nat j) ltac:(rewrite RQ; unfold HEAD; lia)) as ((Hh & b & Hbb) & _).
  split; [exact Hh|]. exists b.
  rewrite <- (fsw_pf_unp B ly S U W mem md (buf + Z.of_nat j) HARU0);
    [exact Hbb | unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia
    | unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia]. }
(* ---- fuzz_realloc's premises ---- *)
assert (HPK : (buf = 0 /\ cap = 0 /\ old = []) \/
   (buf <> 0 /\ (exists U1 U2, U = U1 ++ (buf - HEAD, HEAD) :: U2) /\
    fs_rblock tfibsegs B ly S W (ms_mem ms') buf cap /\ Z.of_nat (length old) = cap /\
    zbytes_at tfibsegs W (ms_mem ms') buf old /\ cap <= live)).
{ destruct (Z.eq_dec cap 0) as [E|E].
  - left. destruct (HCZ E) as (Hb & _). split; [exact Hb|]. split; [exact E|]. unfold old. rewrite E. reflexivity.
  - right. destruct (HCB E) as (Hin & Hb & Hcp & Hbc & Hbs). destruct (HOLD E) as (Hl & Hz).
    destruct (HCN E) as (_ & (_ & Hb16 & _ & Vh) & _).
    split; [unfold HEAD in Hb; lia|]. split; [exact (in_split _ _ (HHEAD E))|].
    split.
    { split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hcp|].
      intros k Hk. rewrite (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling _ SB) by (unfold HEAD in *; lia).
      exact (Vh k Hk). }
    split; [rewrite Hl; lia|]. split; [exact Hz | exact HCL]. }
assert (HGc : fs_glob tfibsegs W (ms_mem ms') live peak cnt fail).
{ assert (VB : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms')) g 8 v).
  { intros g v Hg1 Hg2 Hv k Hk. rewrite (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling _ SB) by lia.
    exact (Hv k Hk). }
  unfold fs_glob, fs_glob_at.
  split; [apply VB; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
  split; [apply VB; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
  split; [apply VB; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
  split; [apply VB; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
  repeat split; lia. }
assert (HEV : (buf = 0 -> st_nev S + EV_fuzz_malloc <= EV_MAX) /\ (buf <> 0 -> st_nev S + 3 <= EV_MAX)).
{ split; intros Hb.
  - destruct (Z.eq_dec cap 0) as [E|E]; [pose proof (Bev0 E); unfold EV_fuzz_malloc; lia|].
    destruct (HCB E) as (_ & Hb' & _). unfold HEAD in Hb'. lia.
  - destruct (Z.eq_dec cap 0) as [E|E]; [destruct (HCZ E); contradiction | exact (Bev3 E)]. }
assert (HBR : cnt <> fail -> blocks_bytes S + (c + HEAD) <= LIVE_MAX).
{ intros Hne. rewrite (HCG Hne) in Bbb.
  assert (Bz : bsz cap <= c + HEAD) by (unfold bsz; destruct (Z.eqb_spec cap 0); unfold HEAD; lia).
  lia. }
assert (HLR : cnt <> fail -> live + c < 2 ^ 64) by (intros Hne; rewrite (HCG Hne) in Blv; lia).
(* the old footprint is FS_PSTAT_FP (image) plus, at cap <> 0, the old block (inFP through wbuf_fp) *)
assert (HFP0 : fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap) FS_PSTAT_FP).
{ intros a Ha. right. right. left. split; [|exact (pgt_pstat_img a Ha)].
  destruct Ha as (r & Hr & Hra). exists r. split; [apply in_or_app; left; exact Hr | exact Hra]. }
(* ---- the call ---- *)
rewrite Ems.
eapply SRr_bind.
{ exact (HREALLOC ly S U W (ms_regs ms') (ms_mem ms') mdc ch1 buf cap c old live peak cnt fail HPREc FH R10 R11
    ltac:(lia) ltac:(unfold MALLOC_MAX, HEAD; lia) HGc HLR ltac:(lia) HPK HEV HBR). }
intros W2 c2 _ HPOST.
destruct HPOST as [(Hcf & HP) | [(Hcf & Hb0 & res & HP) | (Hcf & Hbn & U1 & U2 & res & HU & HP)]].
- (* ======== refused (cnt = fail) ======== *)
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10r & HAB & FH2 & HGL2).
  destruct (pgt_resume FS_PSTAT_FP 0 ly2 S2 U W2 regs2 mem2 md2 0 0 HJc HFP0 OK2 PO2 HPR2)
    as (HJ2 & HARU2 & KEEPE & HS1).
  destruct (pgt_src_after FS_PSTAT_FP 0 ly2 S2 U W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a Ha; left; exact Ha) ltac:(intros p k Hp _; rewrite HAB; exact Hp) ltac:(intros r Hr; left; exact Hr))
    as (_ & _ & _ & _ & SKEEP & _).
  (* o's buffer as it stands after the call: the old block is live at both ends and off FS_PSTAT_FP *)
  assert (HCASE2 : (cap = 0 /\ buf = 0 /\ text = []) \/
    ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ fs_rblock tfibsegs B ly2 S2 W2 mem2 buf cap /\
     Z.of_nat (length text) < cap /\ zbytes_at tfibsegs W2 mem2 buf (text ++ [0]))).
  { destruct (Z.eq_dec cap 0) as [E|E]; [left; destruct (HCZ E) as (Hb & Ht); split; [exact E | split; assumption]|right].
    destruct (HCN E) as (Hj & (Hin & Hb16 & Hcp & Vh) & Hlt & Hzt).
    destruct (HCB E) as (_ & Hb & _ & Hbc & Hbs).
    pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
    assert (Hin2 : In (buf - HEAD, cap + HEAD) (ablocks B ly2 S2)) by (rewrite HAB; exact Hin).
    assert (KB : forall i, 0 <= i < cap + HEAD ->
      mbyte tfibsegs (mrestrict (w_H W2) mem2) (buf - HEAD + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (buf - HEAD + i)).
    { intros i Hi.
      rewrite <- (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling (buf - HEAD + i) SB) by (unfold HEAD in *; lia).
      apply (mbyte_of_aview tfibsegs).
      rewrite <- (aview_at tfibsegs (w_H W2) (unpoison U mem2) mem2 (buf - HEAD + i))
        by (apply (fsw_pf_unp B ly2 S2 U W2 mem2 md2 (buf - HEAD + i) HARU2);
            unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia).
      rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms')) (ms_mem ms') (buf - HEAD + i))
        by (apply (fsw_pf_unp B ly S U W (ms_mem ms') mdc (buf - HEAD + i) HARU);
            unfold in_app, HEAD, SHADOW_OFF, kLowShadowBeg in *; lia).
      apply (F2 (buf - HEAD) (cap + HEAD) i Hin Hin2 ltac:(rewrite RQ; lia)).
      intros Hf. apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) (buf - HEAD + i)
        HAR Hin); [rewrite RQ; lia | exact (pgt_pstat_img _ Hf)]. }
    split; [exact Hj|]. split; [|split; [exact Hlt|]].
    - split; [exact Hin2|]. split; [exact Hb16|]. split; [exact Hcp|].
      intros k Hk. rewrite (KB (Z.of_nat k)) by (unfold HEAD; lia). exact (Vh k Hk).
    - unfold zbytes_at in Hzt |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) Hzt).
      intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
      replace a with (buf - HEAD + (a - (buf - HEAD))) by lia. apply KB. unfold HEAD. lia. }
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_refused 0 ly2 S2 W2 regs2 mem2 md2 0 (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10r KEEPE HCASE2 SKEEP HGL2 ltac:(rewrite HWV; destruct (cap =? 0); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), buf, U.
  split; [reflexivity|]. split; [left; split; reflexivity|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_eq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { apply put_grow_kept_refused; [unfold WMAX; lia | lia | lia |].
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HAB. lia. }
  split; [left; split; [reflexivity | split; [reflexivity | rewrite HAB; reflexivity]]|].
  split; [exact HWK|].
  split; [|exact HSK'].
  exists peak. split; [lia|]. rewrite Z.mod_small by lia. replace (live + cap - cap) with live by lia. exact HGL'.
- (* ======== granted from a NULL buffer (cap = 0) ======== *)
  assert (Hc0 : cap = 0)
    by (destruct (Z.eq_dec cap 0) as [E|E]; [exact E | destruct (HCB E) as (_ & Hb & _); unfold HEAD in Hb; lia]).
  destruct (HCZ Hc0) as (_ & Ht0).
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10g & Hres & HAB & FH2 & HRB2 & HGL2).
  set (Unew := U ++ [(res - HEAD, HEAD)]) in *.
  destruct (pgt_resume FS_PSTAT_FP 1 ly2 S2 Unew W2 regs2 mem2 md2 res (res + Z.of_nat (length text) + n)
    HJc HFP0 OK2 PO2 HPR2) as (HJ2 & HARU2 & KEEPE & HS1).
  assert (Hin2 : In (res - HEAD, c + HEAD) (ablocks B ly2 S2))
    by (rewrite HAB; apply in_or_app; right; left; reflexivity).
  assert (HNEW : ~ In (res - HEAD, c + HEAD) (ablocks B ly S)).
  { intros Hx. pose proof (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hin2) as (_ & _ & _ & _ & _ & PW & _).
    rewrite HAB in PW. apply (pgt_new_once (ablocks B ly S) [] (res - HEAD, c + HEAD) ltac:(cbn [snd]; unfold HEAD; lia) PW).
    rewrite app_nil_r. exact Hx. }
  destruct (pgt_src_after FS_PSTAT_FP 1 ly2 S2 Unew W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a Ha; left; exact Ha)
    ltac:(intros p k Hp _; rewrite HAB; apply in_or_app; left; exact Hp)
    ltac:(intros r Hr; unfold Unew in Hr; apply in_app_or in Hr as [Hr | [<- | []]]; [left; exact Hr | right];
          exists (c + HEAD); cbn [fst snd]; split; [exact Hin2|]; split; [exact HNEW|]; split; [reflexivity|];
          rewrite RQc; unfold HEAD; lia))
    as (HZS2 & SRA2 & SHULL2 & SAMR & SKEEP & SNEW).
  assert (SDISJ : forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)).
  { intros x Hx Hxr. apply (SNEW (res - HEAD) (c + HEAD) Hin2 HNEW ltac:(unfold HEAD; lia) x Hx).
    rewrite RQc. unfold HEAD in *. lia. }
  assert (HTXT : zbytes_at tfibsegs W2 mem2 res text) by (rewrite Ht0; unfold zbytes_at; apply garr8_nil).
  assert (HGLOB2 : fs_glob tfibsegs W2 mem2 (live - cap + c) (Z.max peak (live - cap + c)) (cnt + 1) fail)
    by (rewrite Hc0; replace (live - 0 + c) with (live + c) by lia; exact HGL2).
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_granted 1 ly2 S2 Unew W2 regs2 mem2 md2 res
      (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10g Hres (HRB2 ltac:(lia)) HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR SDISJ SKEEP HGLOB2 Hcj
      ltac:(rewrite HWV, (proj2 (Z.eqb_eq cap 0) Hc0); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), res, Unew.
  split; [reflexivity|]. split; [right; right; split; [exact Hc0 | reflexivity]|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { unfold wbudget_kept. split; [unfold WMAX; lia|]. split; [|rewrite Z.mod_small by lia; lia].
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HAB, YCbq.bsum_app, Bc, Hc0, put_grow_bsz_0.
    change (YCbq.bsum [(res - HEAD, c + HEAD)]) with (c + HEAD + 0). lia. }
  split.
  { right. left. split; [exact Hc0|]. exists (ablocks B ly S), []. split; [rewrite HAB; reflexivity | apply app_nil_r]. }
  split; [exact HWK|].
  split; [|exact HSK'].
  exists (Z.max peak (live - cap + c)). split; [lia|].
  replace (live + c - cap) with (live - cap + c) by lia. rewrite Z.mod_small by lia. exact HGL'.
- (* ======== granted from a live buffer (cap <> 0) ======== *)
  assert (Hcn : cap <> 0) by (intros E; destruct (HCZ E); contradiction).
  destruct (HCB Hcn) as (Hin & Hb & Hcp & Hbc & Hbs).
  destruct (HCN Hcn) as (_ & HRB & Hlt & Hzt).
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HPR2 & R10g & Hres &
    (b1 & b2 & c1 & c2' & HA & HA' & Hcc) & FH2 & HRB2 & HZR & HGL2).
  set (Unew := U1 ++ U2 ++ [(res - HEAD, HEAD)]) in *.
  assert (RQ : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
  assert (Bcap : bsz cap = cap + HEAD) by (unfold bsz; rewrite (proj2 (Z.eqb_neq cap 0) Hcn); reflexivity).
  assert (HFP : fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap)
                  (FS_PSTAT_FP ++ ablocks_fp [(buf - HEAD, cap + HEAD)])).
  { intros a (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
    - right. right. left. split; [exists r; split; [apply in_or_app; left; exact Hr | exact Hra]|].
      exact (pgt_pstat_img a (ex_intro _ r (conj Hr Hra))).
    - unfold ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      left. split; [|exists (buf - HEAD), (cap + HEAD); split; [exact Hin | exact Hra]].
      exists (buf - HEAD, buf + cap). split.
      + apply in_or_app. right. unfold wbuf_fp. rewrite (proj2 (Z.eqb_neq cap 0) Hcn). left. reflexivity.
      + cbn [fst snd]. rewrite RQ in Hra. unfold HEAD in *. lia. }
  destruct (pgt_resume _ 3 ly2 S2 Unew W2 regs2 mem2 md2 res (res + Z.of_nat (length text) + n) HJc HFP OK2 PO2 HPR2)
    as (HJ2 & HARU2 & KEEPE & HS1).
  assert (Hin2 : In (res - HEAD, c + HEAD) (ablocks B ly2 S2))
    by (rewrite HA'; apply in_or_app; right; left; reflexivity).
  assert (HNEW : ~ In (res - HEAD, c + HEAD) (ablocks B ly S)).
  { pose proof (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ (proj1 HARU2) Hin2) as (_ & _ & _ & _ & _ & PW & _).
    rewrite HA' in PW. pose proof (pgt_new_once c1 c2' (res - HEAD, c + HEAD) ltac:(cbn [snd]; unfold HEAD; lia) PW) as NO.
    rewrite Hcc in NO. intros Hx. rewrite HA in Hx. apply in_app_or in Hx as [Hx | [Hx | Hx]].
    - apply NO. apply in_or_app. left. exact Hx.
    - injection Hx as _ Hx. lia.
    - apply NO. apply in_or_app. right. exact Hx. }
  destruct (pgt_src_after _ 3 ly2 S2 Unew W2 mem2 md2 HJc HARU2 FH2
    ltac:(intros a (r & Hr & Hra); apply in_app_or in Hr as [Hr | Hr]; [left; exists r; split; assumption|];
          right; split; [exact Hcn|]; unfold ablocks_fp in Hr; cbn [map In] in Hr; destruct Hr as [<- | []];
          cbn [fst snd] in Hra; rewrite RQ in Hra; unfold HEAD in *; lia)
    ltac:(intros p k Hp Hpn; rewrite HA in Hp; rewrite HA';
          assert (Hp' : In (p, k) (b1 ++ b2))
            by (apply in_app_or in Hp as [Hp | [Hp | Hp]];
                [apply in_or_app; left; exact Hp | injection Hp as Hp _; exfalso; lia | apply in_or_app; right; exact Hp]);
          rewrite <- Hcc in Hp'; apply in_app_or in Hp' as [Hp' | Hp']; apply in_or_app;
          [left; exact Hp' | right; right; exact Hp'])
    ltac:(intros r Hr; unfold Unew in Hr; apply in_app_or in Hr as [Hr | Hr];
          [left; rewrite HU; apply in_or_app; left; exact Hr|];
          apply in_app_or in Hr as [Hr | [<- | []]]; [left; rewrite HU; apply in_or_app; right; right; exact Hr | right];
          exists (c + HEAD); cbn [fst snd]; split; [exact Hin2|]; split; [exact HNEW|]; split; [reflexivity|];
          rewrite RQc; unfold HEAD; lia))
    as (HZS2 & SRA2 & SHULL2 & SAMR & SKEEP & SNEW).
  assert (SDISJ : forall x, s <= x < s + n -> ~ (res - HEAD <= x < res + c)).
  { intros x Hx Hxr. apply (SNEW (res - HEAD) (c + HEAD) Hin2 HNEW ltac:(unfold HEAD; lia) x Hx).
    rewrite RQc. unfold HEAD in *. lia. }
  (* the text in the new buffer: fuzz_realloc kept the old buffer's cap bytes, whose first len are the text *)
  assert (HTXT : zbytes_at tfibsegs W2 mem2 res text).
  { destruct (HOLD Hcn) as (Hlo & Hzo).
    rewrite Z.min_l in HZR by lia. rewrite <- Hlo, firstn_all in HZR.
    assert (Hzt' : zbytes_at tfibsegs W (ms_mem ms') buf (text ++ [0])).
    { unfold zbytes_at in Hzt |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) Hzt).
      intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
      apply (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling a SB). unfold HEAD in *. lia. }
    unfold zbytes_at in HZR, Hzo, Hzt' |- *. intros j Hj.
    assert (Hjo : (j < length old)%nat) by (rewrite Hlo; apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
    assert (Hjt : (j < length (text ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (pgt_garr8_nth _ buf (text ++ [0]) old j Hzt' Hzo Hjt Hjo) as Ej.
    rewrite app_nth1 in Ej by exact Hj. rewrite Ej. exact (HZR j Hjo). }
  rewrite R1.
  eapply SRr_mono.
  { exact (pgt_granted 3 ly2 S2 Unew W2 regs2 mem2 md2 res
      (wevk cap (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs))
      HJ2 HARU2 HS1 HPR2 R10g Hres (HRB2 ltac:(lia)) HNEW FH2 HTXT KEEPE HZS2 SRA2 SHULL2 SAMR SDISJ SKEEP HGL2 Hcj
      ltac:(rewrite HWV, (proj2 (Z.eqb_neq cap 0) Hcn); cbv beta iota; lia)). }
  intros W' c' _ HQ.
  destruct HQ as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & OK' & PO' & HP' & (-> & -> & HWO & HWK & HGL' & HSK')).
  unfold put_post. exists (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs), res, Unew.
  split; [reflexivity|]. split; [right; left; exists U1, U2; split; [exact HU | reflexivity]|].
  unfold wpost, fpostU. exists ly2, S2, regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP'|].
  rewrite HPUT, (proj2 (Z.eqb_neq _ _) Hcf).
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  split; [exact HWO|].
  split.
  { unfold wbudget_kept. split; [unfold WMAX; lia|]. split; [|rewrite Z.mod_small by lia; lia].
    assert (Eb : YCbq.bsum c1 + YCbq.bsum c2' = YCbq.bsum b1 + YCbq.bsum b2)
      by (rewrite <- !YCbq.bsum_app, Hcc; reflexivity).
    rewrite (pgt_bb ly2 S2), (pgt_bb ly S), HA, HA', !YCbq.bsum_app, !YCbq.bsum_cons. cbn [snd].
    rewrite Bc, Bcap. lia. }
  split.
  { right. right. exists b1, b2, c1, c2'. split; [exact HA|]. split; [exact HA' | exact Hcc]. }
  split; [exact HWK|].
  split; [|exact HSK'].
  exists (Z.max peak (live - cap + c)). split; [lia|].
  replace (live + c - cap) with (live - cap + c) by lia. rewrite Z.mod_small by lia. exact HGL'.
Qed.

End pgt.
