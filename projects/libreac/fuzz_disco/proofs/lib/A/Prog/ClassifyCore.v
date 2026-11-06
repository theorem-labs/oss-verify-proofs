(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and module names changed; 3511 of its 3597 lines of code are new or changed and 761 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacArbitrate.v, with its module paths and module names changed; 112 of its 147 lines of code are new or changed and 3562 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacPortsParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_classify_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition CLS_FRAME : Z := 176.
Definition CLS_PARSE_NEED : Z := 144 + 2 * ESTACK.
Definition CLS_OWN_BCMP : Z := CLS_FRAME + 2 * ESTACK.
Definition CLS_VIA_PARSE : Z := CLS_FRAME + CLS_PARSE_NEED.
Definition CLS_STK : Z := Z.max CLS_OWN_BCMP CLS_VIA_PARSE.
Definition EV_CLS : Z := 0.
Definition CLS_DEPTH : Z := 8.

Definition cls_bytes (l : list byte) : list Z := map (fun b : byte => bv_unsigned b) l.

Definition cls_wr (lk o : Z) (L : option (list byte)) (a : Z) : Prop :=
(o <= a < o + 24) \/ (match L with None => False | Some _ => lk <= a < lk + 12 end).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition cls_read (W : world SEGS) (memc : word -> option byte) (sp p n : Z) : Prop :=
0 <= p /\ p + n <= 2 ^ 63 /\ amem_range p n /\
(sp <= p \/ p + n <= sp - CLS_STK) /\
(forall a, p <= a < p + n -> apresent (w_H W) memc a) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p n /\
shadow_hull_vis (aview SEGS (w_H W) memc) p n.

Section h.
Variable treac_ctrl_parse_spec : asyms -> Prop.
Variable treac_ctrl_checksum_verify_spec : asyms -> Prop.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ABCMP : forall fq, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis AMEMCPY : forall fq, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ASM2 : forall fq, astack_malloc_realizes (fx := fq) SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TPARSE : treac_ctrl_parse_spec B.
Hypothesis TCHK : treac_ctrl_checksum_verify_spec B.
Hypothesis TPORTS : treac_ports_parse_spec B.

Definition cls_write (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (p n : Z) : Prop :=
forall a, p <= a < p + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a.

Definition cls_sep (lyc : alayout) (Sc : astate) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\
   frame_addr lyc cid pos <= p /\ p + n <= frame_addr lyc cid pos + fs_frame_bytes cid)
\/ (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p /\ p + n <= b + req_size m)
\/ (ly_stk_lo lyc <= p /\ p + n <= ly_stk_hi lyc).

Definition tcls_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(W2 : world SEGS) (mem2 : word -> option byte) (sp lk o : Z) (L : option (list byte)) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - CLS_STK <= a < sp) -> ~ cls_wr lk o L a ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ cls_wr lk o L (b + i) ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ cls_wr lk o L a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - CLS_STK <= a < sp) ->
apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - CLS_STK <= a < sp -> apresent (w_H W2) mem2 a).

Definition tcls_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (lk o len : Z) (FB U OB : list byte) (L : option (list byte))
: world SEGS -> config -> Prop :=
fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fq) k) /\
(@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CLS) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
getr regs2 10 = w64 (disco_classify_c.cm_ret FB len U L) /\
garr8 SEGS (mrestrict (w_H W2) mem2) o (cls_bytes (disco_classify_c.cm_out FB len U L OB)) /\
(forall Lb, disco_classify_c.cm_lock FB len U L = Some Lb ->
garr8 SEGS (mrestrict (w_H W2) mem2) lk (cls_bytes Lb)) /\
tcls_kept lyc Sc W memc W2 mem2 (spZ regs) lk o L.

Definition tcls_entry (a : Z) : Prop :=
forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
(lk f len u o : Z) (FB U OB : list byte) (L : option (list byte)),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 lk -> getr regs 11 = w64 f -> getr regs 12 = w64 len ->
getr regs 13 = w64 u -> getr regs 14 = w64 o ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLS_STK -> spZ regs <= sp0 ->
spZ regs + 32 <= ly_top lyc ->
Z.of_nat (length (frames Sc)) <= CLS_DEPTH ->
0 <= len < 2 ^ 64 ->
length FB = 50%nat -> length U = 6%nat -> length OB = 24%nat ->
(50 <= len -> 0 < f /\ cls_read W memc (spZ regs) f 50 /\ cls_sep lyc Sc f 50 /\
garr8 SEGS (mrestrict (w_H W) memc) f (cls_bytes FB)) ->
cls_read W memc (spZ regs) u 6 -> cls_sep lyc Sc u 6 ->
garr8 SEGS (mrestrict (w_H W) memc) u (cls_bytes U) ->
0 < o -> o mod 4 = 0 ->
cls_read W memc (spZ regs) o 24 ->
garr8 SEGS (mrestrict (w_H W) memc) o (cls_bytes OB) ->
cls_write STK sp0 FP ly S lyc Sc own o 24 ->
o + 24 <= ly_stk_lo lyc \/ ly_stk_hi lyc <= o ->
(match L with
 | None => lk = 0
 | Some Lb => 0 < lk /\ lk mod 4 = 0 /\ length Lb = 12%nat /\
   cls_read W memc (spZ regs) lk 12 /\
   garr8 SEGS (mrestrict (w_H W) memc) lk (cls_bytes Lb) /\
   cls_write STK sp0 FP ly S lyc Sc own lk 12 /\
   (lk + 12 <= ly_stk_lo lyc \/ ly_stk_hi lyc <= lk)
 end) ->
(o + 24 <= u \/ u + 6 <= o) ->
(50 <= len -> o + 24 <= f \/ f + 50 <= o) ->
(match L with
 | None => True
 | Some _ => (lk + 12 <= o \/ o + 24 <= lk) /\ (lk + 12 <= u \/ u + 6 <= lk) /\
   (50 <= len -> lk + 12 <= f \/ f + 50 <= lk)
 end) ->
SRr SEGS W (cfg_at (fx := fq) SEGS a regs memc mdc)
(tcls_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs lk o len FB U OB L).

Definition tclassify_core_spec : Prop := tcls_entry (BASE + AF_classify_core).

End h.
End f.
End d.
