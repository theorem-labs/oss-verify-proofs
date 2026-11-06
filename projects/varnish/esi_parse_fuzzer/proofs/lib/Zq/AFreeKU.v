(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ANodijx ANod9v0 APgGeo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS AFreeR.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.ARt4ak4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.ARt4bhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4tam OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.AFreeC2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

Section DoRecK.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (rax sp : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (lo T b cnt i : Z) (scr : list byte) (cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word).
  (* [comment removed for export] *)
  Variables (tsd ctx thr sb ri : Z).

  Let CBPRIM : cbrec_prim2_stmt. Proof. exact cbrec_prim_ok. Qed.   (* [comment removed for export] *)

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPE : tp = wz TP.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis PCo : poison_consts m.
  Hypothesis THRA : thr mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BAL : b mod 8 = 0.
  Hypothesis CNTB : 0 <= cnt <= 1021.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_sr : sb + 2^37 <= ri.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SEP_cs : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_bt : apart b 8192 thr 4096.
  Hypothesis SEP_bc : apart b 8192 ctx 0x10000.
  Hypothesis SEP_br : apart b 8192 ri 4096.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m RI_PTR [C8 (wz ri)].
  (* [comment removed for export] *)
  Hypothesis DF : rw_cells rsegs m (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0).
  Hypothesis TR : alloc_ceiling <= T.   (* [comment removed for export] *)
  Hypothesis TU : bv_unsigned sp + 112 <= T.
  (* [comment removed for export] *)
  Variable kb : Z.
  Hypothesis BFORM : b = sb + 24 * 2^32 + 16 * kb.
  Hypothesis KBR : 0 <= kb /\ 16 * kb + 8192 <= 3758096384.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma kcbc_ro : forall (mm : word -> option byte),
    rw_cells rsegs mm (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    ro_cells rsegs mm (bv_unsigned sp + 8) [C8 (wz C)].
  Proof.
    intros mm H. unfold dorec_frame in H.
    apply (rw_cells_app_split mm (bv_unsigned sp) [CB 8 scr] _) in H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    exact (rw_ro_prefix1 mm _ _ _ H).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma kiter_sec_pre : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' pw hl hlb hlm hls : word)
      (mh pa u1 u2 srt h msz csz idx nf ca gA gM nsz st b1 rf rfd mu md sealed : Z) (hs : list word) (old : list byte),
    let n := Z.of_nat (length hs) in let hla := bv_unsigned hl in
    lo <= bv_unsigned sp - 112 -> 0 <= i < cnt -> bv_unsigned pw = mh ->
    aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> pa mod 8 = 0 -> 1 <= n < 2^20 ->
    0 <= u1 < 256 -> 0 <= u2 < 2^15 -> 0 <= srt < 256 -> 0 <= idx < n ->
    nth_error hs (Z.to_nat idx) = Some (wz h) -> nth_error hs (Z.to_nat (n - 1)) = Some hl ->
    aobj hla 32 -> hla + 32 <= alloc_ceiling -> hla mod 8 = 0 ->
    0 <= nf < 2^64 -> 0 <= ca < 2^64 -> 0 <= gA < 2^64 -> 0 <= gM < 2^64 -> 0 <= csz < 2^64 ->
    aobj h msz -> h mod 4096 = 0 -> 4096 + 32 <= msz -> msz mod 4096 = 0 -> h + msz <= alloc_ceiling ->
    apart h msz sb (2^37) -> h + 32 <= mh /\ mh + 16 <= h + msz -> nearest hs mh = h -> 0 <= nsz < 2^32 -> 0 <= st < 256 -> 0 <= b1 < 256 ->
    0 <= rf < 2^64 -> 0 <= rfd < 2^64 -> 0 <= mu < 2^64 -> 0 <= md < 2^64 -> sealed <> 0 /\ 0 <= sealed < 2^64 ->
    apart h msz pa (8 * n) -> apart hla 32 pa (8 * n) -> apart h msz thr 4096 -> apart h msz ctx 0x10000 ->
    apart pa (8 * n) thr 4096 -> apart pa (8 * n) ctx 0x10000 -> apart hla 32 thr 4096 -> apart hla 32 ctx 0x10000 ->
    apart b 8192 pa (8 * n) -> apart b 8192 hla 32 ->
    a8_pbeg h < a8_pend h msz ->
    ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)] -> ro_cells rsegs m 0xa8bb0 [C8 (wz sealed)] ->
    rw_cells rsegs m (b + 24 + 8 * i) [C8 pw] ->
    rw_cells rsegs m 0xb15d0 [C8 (wz n); C1 (Z_to_bv 8 srt)] ->
    rw_cells rsegs m 0xb15e8 [C8 (wz nf); C8 (wz ca)] ->
    rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    rw_cells rsegs m 0xb1818 [C8 (wz gA); C8 (wz gM)] ->
    u64arr rsegs m pa hs ->
    rw_cells rsegs m h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
    (hla = h \/ ((h + 32 <= hla \/ hla + 32 <= h) /\ rw_cells rsegs m hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (n - 1))])) ->
    ro_cells rsegs m mh [C1 (Z_to_bv 8 st); C1 (Z_to_bv 8 b1); C2 (wz (size_hi nsz)); C4 (wz nsz)] ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    rw_cells rsegs m (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
    rw_cells rsegs m (sh h) [CB (Z.to_nat (msz / 8)) old] ->
    (forall (t0'' t1'' t2'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        rw_cells rsegs m' (bv_unsigned sp + -32) [C8 (wz LMA_L); C8 (wz 0xb1558); C8 (wz T); C8 (wz dorec_retpc)] ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
        rw_cells rsegs m' (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
        bytes_at rsegs m' (sh h) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8))) ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (0xb1800, 0xb1804); (thr + 2840, thr + 2856); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8);
               (0xb1818, 0xb1828); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32); (sh h, sh h + msz / 8); (thr + 2888, thr + 2904)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -32) ->
        Q (MSsvc (mkR (wz ldealloc_resume) (wz (bv_unsigned sp + -32)) gp tp t0'' t1'' t2'' (wz h) (wz h)
                      (wz (a8_pbeg h)) (wz (a8_len h msz)) (wz 4) (wz 4) a4'' a5'' a6'' (wz 233)
                      (wz msz) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3'' t4'' t5'' t6'')
                 F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' i) F (wz dorec_callblk) fc None m (seg_rom rsegs)).
  Proof.
    intros until old. cbv zeta. intros LOLE IR PW PALO PAHI PAAL NR U1R U2R SRTR IDX NTH NTL HLLO HLHI HLAL NFR CAR GAR GMR CSR
           HLO HAL MSZ MSZAL HHI HSB MHR NRST NSZ STR B1R RFR RFDR MUR MDR SEALR SEP_hp SEP_lp SEP_ht SEP_hc SEP_pt SEP_pc SEP_lt SEP_lc SEP_bpa SEP_bl
           NEI CLMA CSEAL ENT NSRT NFCA LCK GAM ARR HDRL HLC HDRU TRF TMU SHC K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold it_regs, kHighMemBeg in *.
    pose proof (kcbc_ro m DF) as CBC.
    (* [comment removed for export] *)
    eapply (dorec_call_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m b i pw); [> try (fside CV) .. | idtac].
    rewrite <- (Z_to_bv_bv_unsigned pw), PW.
    (* [comment removed for export] *)
    eapply (sdeal_pre _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m
              lo (bv_unsigned sp + 8) mh sb pa u1 u2 srt h msz csz idx nf ca gA gM nsz st b1 tsd ctx thr rf rfd mu md sealed hs hl hlb hlm hls);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcell | right; lia | zmod | assumption]).
    intros t0c t1c t2c a4c a5c a6c t3c t4c t5c t6c m2 UF NSRT2 NFCA2 LCK2 GAM2 ARR2 HDRL2 HLC2 TRF2 TMU2 SHZ MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in UF, MU2, ST2 by lia. unfold sdeal_W, sdeal_prefix_W in MU2. cbn [app] in MU2. rewrite ?unsigned_lit in MU2 by lia.
    (* [comment removed for export] *)
    assert (HQ : h = 4096 * (h / 4096)) by (pose proof (Z_div_mod_eq_full h 4096) as X; rewrite HAL in X; lia).
    assert (MQ : msz = 4096 * (msz / 4096)) by (pose proof (Z_div_mod_eq_full msz 4096) as X; rewrite MSZAL in X; lia).
    set (hq := h / 4096) in HQ. set (mq := msz / 4096) in MQ. clearbody hq mq.
    assert (SHE : sh h = 512 * hq + 2147450880).
    { unfold sh, kShadowOffset. rewrite HQ. replace (4096 * hq) with ((512 * hq) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    assert (SZ8 : msz / 8 = 512 * mq) by (rewrite MQ at 1; replace (4096 * mq) with ((512 * mq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    pose proof MU2 as MUX. rewrite SHE, SZ8 in MUX.
    pose proof DF as DF2. xfer DF2 MUX WM2. pose proof ENT as ENT2. xfer ENT2 MUX WM2. clear MUX.
    unfold madvise_ecall_pc, ldealloc_resume, LMA_L, LMA_STAT in *.
    eapply K.
    all: first [kcell | exact HLC2 | exact MU2 | exact WM2 | eassumption].
  Qed.


  (* [comment removed for export] *)
  Lemma kiter_sec_mid : forall (Q : machine_state -> Prop) (m7 : word -> option byte)
      (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pw hl hlb hlm hls : word)
      (mh pa u1 u2 srt h msz csz idx nf ca gA gM nsz st b1 rf rfd mu md sealed : Z) (hs : list word),
    let n := Z.of_nat (length hs) in let hla := bv_unsigned hl in
    lo <= bv_unsigned sp - 112 -> 0 <= i < cnt ->
    aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> 1 <= n < 2^20 -> 0 <= idx < n ->
    aobj hla 32 -> hla + 32 <= alloc_ceiling ->
    aobj h msz -> h mod 4096 = 0 -> 4096 + 32 <= msz -> msz mod 4096 = 0 -> h + msz <= alloc_ceiling ->
    apart h msz sb (2^37) -> h + 32 <= mh /\ mh + 16 <= h + msz -> 0 <= mu < 2^64 -> 0 <= md < 2^64 -> sealed <> 0 /\ 0 <= sealed < 2^64 ->
    apart h msz pa (8 * n) -> apart hla 32 pa (8 * n) -> apart h msz thr 4096 -> apart h msz ctx 0x10000 ->
    apart pa (8 * n) thr 4096 -> apart pa (8 * n) ctx 0x10000 -> apart hla 32 thr 4096 -> apart hla 32 ctx 0x10000 ->
    apart b 8192 pa (8 * n) -> apart b 8192 hla 32 ->
    mem_inv rsegs m7 -> stk rsegs m7 lo (bv_unsigned sp + -32) ->
    thread_cells m7 tp tsd ctx thr ->
    rw_cells rsegs m7 (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m7 (b + 24 + 8 * i) [C8 pw] ->
    rw_cells rsegs m7 (bv_unsigned sp + -32) [C8 (wz LMA_L); C8 (wz 0xb1558); C8 (wz T); C8 (wz dorec_retpc)] ->
    rw_cells rsegs m7 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m7 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
    rw_cells rsegs m7 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    rw_cells rsegs m7 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
    u64arr rsegs m7 pa (upd hs (Z.to_nat idx) hl) ->
    rw_cells rsegs m7 h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
    (hla = h \/ rw_cells rsegs m7 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
    rw_cells rsegs m7 (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
    rw_cells rsegs m7 (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
    (forall (t0'' t1'' t2'' a3'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (uscr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        rw_cells rsegs m' (bv_unsigned sp + -48) (unmap_frame uscr (wz LMA_L) (wz 0xb1558) (wz T) (wz dorec_retpc)) ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
        rw_cells rsegs m' (thr + 2888) [C8 (wz (mu + 1)); C8 (wz (md + msz))] ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (thr + 2888, thr + 2904)] m7 m' ->
        wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -48) ->
        Q (MSsvc (mkR (wz unmap_resume) (wz (bv_unsigned sp + -48)) gp tp t0'' t1'' t2'' (wz msz) (wz 0)
                      (wz h) (wz msz) (wz 0) a3'' a4'' a5'' a6'' (wz 215)
                      (wz h) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3'' t4'' t5'' t6'')
                 F (wz munmap_ecall_pc) (wz 215) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz ldealloc_resume) (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' (wz h) (wz h)
                        (wz 0) a1' a2' a3' a4' a5' a6' a7'
                        (wz msz) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3' t4' t5' t6')
                    F (wz madvise_after_pc) fc None m7 (seg_rom rsegs)).
  Proof.
    intros until hs. cbv zeta. intros LOLE IR PALO PAHI NR IDX HLLO HLHI HLO HAL MSZ MSZAL HHI HSB MHR MUR MDR SEALR
           SEP_hp SEP_lp SEP_ht SEP_hc SEP_pt SEP_pc SEP_lt SEP_lc SEP_bpa SEP_bl MI7 ST7 TC7
           DF7 ENT7 DLF NSRT7 NFCA7 LCK7 GAM7 ARR7 HDRL7 HLC7 TRF7 TMU7 K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC7 as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    clear MI ST TC PCo CSB CRI DF.
    unfold kHighMemBeg in *.
    eapply sdeal_mid with (sp := sp) (lo := lo) (cb := bv_unsigned sp + 8) (mh := mh) (pa := pa) (u1 := u1) (u2 := u2) (h := h) (msz := msz) (csz := csz)
             (idx := idx) (nf := nf) (ca := ca) (gA := gA) (gM := gM) (nsz := nsz) (tsd := tsd) (ctx := ctx) (thr := thr) (rf := rf) (rfd := rfd)
             (mu := mu) (md := md) (sealed := sealed) (hs := hs) (hl := hl) (hlb := hlb) (hlm := hlm) (hls := hls);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcell | right; lia | zmod | assumption]).
    intros t0c t1c t2c a3c a4c a5c a6c t3c t4c t5c t6c uscr m2 UF NSRT2 NFCA2 LCK2 GAM2 ARR2 HDRL2 HLC2 TRF2 TMU2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in UF, MU2, ST2 by lia. rewrite ?unsigned_lit in MU2 by lia.
    pose proof DF7 as DF2. xfer DF2 MU2 WM2. pose proof ENT7 as ENT2. xfer ENT2 MU2 WM2.
    unfold unmap_frame, munmap_ecall_pc, unmap_resume, LMA_L, LMA_STAT in *.
    eapply K.
    all: first [kcell | exact HLC2 | exact MU2 | exact WM2 | eassumption].
  Qed.
End DoRecK.
