(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of
   segments S11 (0x85868 .. 0x85980: the probe loop, the "nosuch0" pair, checks 24 and 25, the UBSan trap branches
   0x858c0 / 0x858c8, calloc(cap + 1, 18)) and S12 (0x85984 .. 0x85990: calloc(cap + 1, 20)) of the test harness's
   entry function LLVMFuzzerTestOneInput (0x84dc0).

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new, ADAPTED from the image-A twin's
   S11 / S12 walk, the image-A G1 walk owner's LLVMFuzzerTestOneInput_s20.v)

   The statements proved: lt_seg_S11_stmt and lt_seg_S12_stmt of LLVMFuzzerTestOneInput_defs.v, each at every FP
   state. S11 is cut at the inner points of LLVMFuzzerTestOneInput_s20k.v (H i, A i, Z i, N, NZ):
     K85868 -> H 0 | N                     s20_L0  (0x85868 .. 0x858ac: check 24, n, the loop's registers)
     H i -> A i                            s20_L1  (the probe in scope, the traps 0x858c0 / 0x858c8,
                                                    snprintf(probe, 18, "%sx", m->seg[i].name))
     A i -> Z i                            s20_L2  (strlen, m_find, and check_absent on a miss)
     Z i -> H (i + 1) | N                  s20_L3  (the probe out of scope, check 25, the latch)
     N -> NZ                               s20_L4  (m_find and check_absent of "nosuch0")
     NZ -> K85984                          s20_L5  (calloc(cap + 1, 18))
     K85984 -> K85994                      s20_S12 (calloc(cap + 1, 20))
   and the loop is closed by downward induction on the turn (m->n <= 32).

   ADOPTED from the image-A twin (the image-A G1 walk owner's S11 / S12 walk, image A's LLVMFuzzerTestOneInput_s20*.v
   as built on its VM, 2026-10-30 18:2x-18:3xZ; image A's registers, slots and pcs renamed to image B's by
   PLAN-asanubsan-main section 11): s20_L0 / s20_L3 and their seeds (its piece s20e), s20_L1 and the snprintf call
   step (its s20c), the calloc walk kit, s20_L5 / s20_S12 (its s20f, itself image A's S01 / S02 kit, commit
   119b28fad68f), the seed / chunk / call-step lemmas of s20_L2 / s20_L4 (its s20d; image B's two
   proofs are new); the shadow-byte reader s20[ab]_zs_ok is image A's S00 walk's (image A's S00 commit
   52ff1753c784). Image B only: the two UBSan trap branches of H i -> A i, decided inside the run by the seed's atom
   ranges (B-DELTA section 2.2 way (a)): 0x858c0 `beq s4,s6` with s4 = i in [0, 31] (i < m->n <= 32, s20_mconf_n)
   and s6 = 32; 0x858c8 `bltu a0,s2` with a0 = ~M from 208(s1) in [2 ^ 63, 2 ^ 64 - 1] (lt_hblk's sa_addr: M + 9236
   <= 2 ^ 63) and s2 = 256 i in [0, 7936]. The stack-protector cells of lt_img at a later point (the .got word gotwA
   is runtime-owned in the regenerated listing, the image-B listing owner's commit ec20d5d4e1df) are re-read from AR at that point by
   SegRecCells.seg_rec_cells, under the Section hypothesis HSY : YF0m.SegBSyms B (the S04 walk's k14_img_kept). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegPaLib SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSegCalloc RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecCells.
(* the symbolic engine and the call steps the segment lemmas use *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0h YK0i YK1b YK1a YK18 YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaSym PaStep PaRun PaShadow PaJournal PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFPf RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGCalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.


(* ================= piece S20Run: s20_L0, s20_L3 (S11 / S12 piece a): definitions and lemmas outside the sections ================= *)

(* ---- the symbolic seeds (every register its own atom; the bytes the code reads as read-only chunks) ----
   K85868 (0x85868): atoms 32 = FR + 192 (the probe), 33 = SH(m + 0x2000), 34 = m, 35 = m + 0x2000, 36 = m->n;
   the s1 slots 120, 176, 192, 216 (one region of s1), the shadow byte of m + 0x2000 (0) and the 4 bytes of m->n *)
Definition s20a_X : sv := SLit SHADOW_OFF.
Definition s20a_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s20a_rgK : smem := [
  YP09.mkRegion (Some 9%nat) 120 224 120 120
    [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SOff 33 0));
     YP09.mkChunk 192 (CVal 8 (SOff 34 0)); YP09.mkChunk 216 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))] ].
Definition s20a_faK : facts := mkFacts [(36%nat, mkAF 0 32 0)] [] [].
Definition s20a_ssK : sstate := mkSS LO_K85868 sr_atoms s20a_rgK None s20a_faK.

(* Z i (0x85908): atoms 32 = SH(FR), 33 = SH(m + 0x2000), 34 = m + 0x2000, 35 = m->n; the probe's three shadow
   bytes SH(FR) + 24 .. 26 (written), the shadow byte of m + 0x2000 (0), the s1 slots 176, 184, 216 and the 4 bytes
   of m->n; s4 = i <= 31, SH(FR) in the shadow band, m->n <= 32 *)
Definition s20a_rgZ : smem := [
  YP09.mkRegion (Some 32%nat) 24 27 24 27 [];
  YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 9%nat) 176 224 176 176
    [YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 184 (CVal 8 (SOff 32 0));
     YP09.mkChunk 216 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 34%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))] ].
(* the token runner's shadow band for Z i: empty (no shadow entry, no token check), so that the run's write window
   SH(FR) + 24 .. 26 passes sh_static_ok (the twin's choice) *)
Definition s20a_spanZ : Z * Z := (0, 0).
Definition s20a_faZ : facts :=
  mkFacts [(20%nat, mkAF 0 31 0); (32%nat, mkAF SHADOW_OFF 0x10007fff8000 0); (35%nat, mkAF 0 32 0)] [] [].
Definition s20a_ssZ : sstate := mkSS LO_Z sr_atoms s20a_rgZ None s20a_faZ.

(* 1-byte literal chunks read back as shadow bytes (image A's S00 walk, s10_c1 .. s10_zs_ok) *)
Definition s20a_c1 (c : YP09.chunk) (off : Z) : option Z :=
match c with
| YP09.mkChunk o (CVal w (SLit z)) =>
  if (Z.eqb o off && N.eqb w 1)%bool then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)) else None
| _ => None
end.
Fixpoint s20a_lit1 (cs : list YP09.chunk) (off : Z) : option Z :=
match cs with
| [] => None
| c :: cs' => match s20a_c1 c off with Some v => Some v | None => s20a_lit1 cs' off end
end.
Fixpoint s20a_zs_b (cs : list YP09.chunk) (off : Z) (l : list Z) : bool :=
match l with
| [] => true
| x :: l' => match s20a_lit1 cs off with Some v => Z.eqb v x && s20a_zs_b cs (off + 1) l' | None => false end
end.
Lemma s20a_lit1_in : forall cs off v, s20a_lit1 cs off = Some v ->
exists z, In (YP09.mkChunk off (CVal 1 (SLit z))) cs /\ v = bv_unsigned (byte_of_word (Z_to_bv 64 z) 0).
Proof.
induction cs as [|c cs IH]; intros off v H; cbn [s20a_lit1] in H; [discriminate H|].
destruct (s20a_c1 c off) as [v'|] eqn:Ec.
- injection H as <-. destruct c as [o cv]. destruct cv as [w e| len | len | d s len]; cbn [s20a_c1] in Ec;
  try discriminate Ec.
  destruct e; try discriminate Ec.
  destruct ((o =? off) && (w =? 1)%N)%bool eqn:Eb; [|discriminate Ec].
  apply andb_prop in Eb as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o w.
  injection Ec as <-. exists z. split; [left; reflexivity | reflexivity].
- destruct (IH off v H) as (z & Hin & Hv). exists z. split; [right; exact Hin | exact Hv].
Qed.


(* ================= piece S20Snp: s20_L1 (S11 / S12 piece b): definitions and lemmas outside the sections ================= *)

(* ======================================= small facts ======================================= *)
(* a reader's value is a byte *)
Lemma s20b_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
(* a callee-saved register a call keeps *)
Lemma s20b_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

(* ================= the snprintf wrapper with one string argument (row 4 at FR_seg), a walk step ================= *)
Section snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
#[local] Notation rdM W mem := (aview segs (w_H W) mem).

(* snprintf(d, n, f, w) for a format f whose one conversion argument is the C string s at w (a3), under row 4 as
   segconf states it (RtPFSeg.v: RtPFCmd.cmd_asnprintf_realizes at FR_seg img_lo gotw, window SEG_SNP_K =
   2 * ESTACK, the return at some FP state). PaRt.v's cwc_aj_snprintf_atSF with: the destination [d, d + n)
   bytes the journal lets the walk write, present and not the runtime's (the caller's side-stack frame, say), below
   the call's window; the format, the stack-protector cells and the read-only ranges below d; the string's bytes,
   its NUL and the slack word after it mapped (sa_str), addressable with 8 bytes past its NUL in application memory,
   apart from the destination and below the window. The step returns at some fx1 with fxrel fx fx1, keeps the
   journal at the same count, writes sn_bytes (n - 1) T at d and its window, and keeps every other byte. *)
Lemma s20b_aj_snprintf_atSF : forall img_lo img_hi cr pc gotw guard,
  @RtPFSeg.seg_asnprintf_realizes fx rc segs B img_lo img_hi cr pc gotw guard ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt qs w s T (o : Z) raw,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f -> getr regsT 13 = w64 w ->
  1 <= n < 2 ^ 31 -> 0 < d ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> RtPFSeg.SEG_SNP_K - o <= STK -> sp0 + o <= 2 ^ 47 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n ->
     awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
     writable_at segs (mrestrict (w_H W) memT) a /\ ~ aowned B lyc Sc a) ->
  d + n <= sp0 + o - RtPFSeg.SEG_SNP_K ->
  sa_addr (rdM W memT) d n -> amem_range d (n + 8) ->
  zdisjoint (d, n) (img_lo, img_hi - img_lo) ->
  Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= d) cr ->
  sa_ssp (rdM W memT) gotw guard -> 0 <= gotw -> gotw + 8 <= d -> 0 <= guard -> guard + 8 <= d ->
  RtDefs.rt_rom_view segs B W memT ->
  0 < f -> sa_zs (rdM W memT) f (fmt ++ [0]) -> sa_addr (rdM W memT) f (Z.of_nat (length fmt) + 1) ->
  img_lo <= f -> f + Z.of_nat (length fmt) + 1 <= gotw -> fmt <> [] ->
  RtPFSeg.seg_parse fmt = Some qs -> RtPFSeg.seg_text qs [RtPFPf.APtr s] = Some T ->
  RtPFSeg.seg_prec_pos qs [RtPFPf.APtr s] ->
  0 < w -> sa_str (rdM W memT) w s -> sa_addr (rdM W memT) w (Z.of_nat (length s) + 1) ->
  amem_range w (Z.of_nat (length s) + 8) -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  zdisjoint (w, RtPFShared.str_end w s - w) (d, n) ->
  RtPFShared.str_end w s <= sp0 + o - RtPFSeg.SEG_SNP_K ->
  Z.of_nat (length T) < 2 ^ 31 - 1 -> frm0 fx ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
  (fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
    c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (getr regs2 10 = w64 (Z.of_nat (length T)) /\
     forall i, 0 <= i < RtPFShared.sn_len (n - 1) T ->
       rdM W mem2 (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o) ->
       ~ (d <= a < d + RtPFShared.sn_len (n - 1) T) -> rdM W mem2 a = rdM W memT a)).
Proof using LAWS segs_low.
intros img_lo img_hi cr pc gotw guard AP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt qs w s T o
  raw HJ Ha0 Ha1 Ha2 Ha3 Hn Hd Hsp' Hal Hneg Hbud Hsp47 Hgp Htp Hra Hraw Hdest Hdw Hdaddr Hdamr Hdog HCR Hssp
  Hgc0 Hgc1 Hgv0 Hgv1 Hrom Hf Hfz Hfaddr Hflo Hfhi Hfne Hparse Htext Hprec Hw Hstr Hwaddr Hwamem Hslen Hwd Hws HT
  Hfrm.
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (len := RtPFShared.sn_len (n - 1) T).
assert (Hlen : 1 <= len <= n).
{ unfold len, RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
destruct Hdaddr as (Hd0 & Hdn & Hdamr0 & Hdrad & Hdhull).
destruct Hfaddr as (Hf0 & Hfn & Hfamr & Hfrad & Hfhull).
destruct Hwaddr as (Hw0 & Hwn & Hwamr & Hwrad & Hwhull).
destruct Hssp as (Hgw & cval & Hcw).
destruct Hstr as ((Hwz & Hwnz) & Hwt).
assert (HPRE : RtDefs.ecall_pre_stk segs B RtPFSeg.SEG_SNP_K lyc Sc W regsT memT mdc).
{ eapply ecall_pre_stk_at; try eassumption; first [lia | rewrite Hra; exact Hraw]. }
destruct HPRE as (HEP & Hslo & Hscr).
(* what the call writes: its window and [d, d + len); everything it reads lies below d *)
assert (HOUT : forall x wd, 0 <= wd -> x + wd <= d ->
  Forall (zdisjoint (x, wd)) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)).
{ intros x wd Hwd0 Hx. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
assert (HSE : Z.of_nat (length s) + 1 <= RtPFShared.str_end w s - w <= Z.of_nat (length s) + 8).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
assert (HWOUT : Forall (zdisjoint (w, RtPFShared.str_end w s - w))
  (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)).
{ unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
(* the string's bytes are bytes, none of them 0 *)
assert (Hsb : Forall (fun c => 0 < c < 256) s).
{ apply Forall_forall. intros c Hc. destruct (In_nth s c 0 Hc) as (j & Hj & Ej).
  pose proof (Hwz j ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
  rewrite app_nth1 in Hb by lia. rewrite Ej in Hb.
  pose proof (s20b_aview_byte _ _ _ _ _ Hb) as Hr.
  assert (Hc0 : c <> 0) by (intros E0; apply Hwnz; rewrite <- E0; exact Hc).
  lia. }
assert (A3 : argZ regsT 3 = w).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite Ha3. unfold w64. apply unsigned_lit_small. lia. }
assert (HARGS : RtPFShared.pf_args_asan (rdM W memT) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)
  (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) [RtPFPf.APtr s]).
{ cbn [map app RtPFShared.pf_args_asan RtPFShared.pf_arg_asan]. rewrite A3.
  split; [|exact I].
  split; [exact Hsb|]. split; [exact Hw|]. split; [exact Hslen|].
  split.
  { intros j Hj. pose proof (Hwz (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  split; [unfold RtPFShared.str_end; exact Hwt|].
  split; [exact HWOUT|]. split; [exact Hwamr|]. split; [exact Hwrad | apply Hwhull; lia]. }
assert (HFR : RtPFSeg.FR_seg img_lo gotw (rdM W memT) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len) f
  (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T).
{ unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam. exists fmt, qs, [RtPFPf.APtr s].
  split.
  { split; [exact Hf|]. split.
    - intros j Hj. pose proof (Hfz (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia. exact Hb.
    - split; [apply HOUT; lia|]. split; [exact Hfamr|]. split; [exact Hfrad | apply Hfhull; lia]. }
  split; [exact Hparse|].
  split; [apply Forall_forall; intros q _; destruct q; exact I|].
  split; [exact HARGS|]. split; [exact Htext|]. split; [exact Hprec|].
  split; [exact Hflo|]. split; [exact Hfhi|].
  split.
  { cbn [map app RtPFCmd.cmd_args_slack]. rewrite A3. split; [|exact I].
    unfold amem_range in *. lia. }
  split; [exact Hfne|].
  cbn [map app RtPFCmd.cmd_args_amem]. rewrite A3. split; [exact Hwamem | exact I]. }
apply (aj_art_own_atF segs B LAWS segs_low RtPFSeg.SEG_SNP_K (fun a => d <= a < d + len) pc W regsT memT STK sp0 FP
  ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
     forall i, 0 <= i < len -> rdM W mem' (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0))
  HJ Hsp' Hal Hneg ltac:(lia) ltac:(lia) Hra).
{ intros a Ha. exact (proj1 (Hdest a ltac:(lia))). }
apply (srr_art_postF_of_pf segs B RtPFSeg.SEG_SNP_K lyc Sc W regsT memT mdc _ d len
  (RtPFShared.sn_bytes (n - 1) T) (Z.of_nat (length T))).
{ intros a Ha. apply Hscr. exact Ha. }
apply (AP lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval HEP).
all: try fold len.
- exact Hslo.
- intros a Ha. apply Hscr. exact Ha.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Hrom.
- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HCR r Hr) as (H1 & H2 & H3). lia.
- apply Forall_forall. intros [x wd] Hr. pose proof (proj1 (Forall_forall _ _) HCR (x, wd) Hr) as (H1 & H2 & H3).
  cbn [fst snd] in *. apply HOUT; lia.
- exact Hgw.
- exact Hcw.
- exact Hgc0.
- lia.
- exact Hgv0.
- lia.
- apply HOUT; lia.
- apply HOUT; lia.
- split; [reflexivity | intros j Hj; cbn [length] in Hj; lia].
- cbn [length]. rewrite Hsp'. lia.
- cbn [length]. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- exact HFR.
- exact Hn.
- exact HT.
- exact Hd.
- lia.
- unfold RtPFShared.snp_out. rewrite HK, Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- intros a Ha. destruct (Hdest a ltac:(lia)) as (_ & Hwr & Hno). split; [exact Hwr|]. split; [exact Hno|].
  rewrite Hsp'. lia.
- unfold amem_range in *. lia.
- intros x Hx. apply Hdrad. lia.
- intros sx Hsx. apply (Hdhull ltac:(lia)). split; [lia|].
  assert (E1 : (d + len - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr in *.
  assert (E2 : (SHADOW_OFF + (d + len - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
- unfold zdisjoint in *. cbn [fst snd] in *. lia.
- exact Hfrm.
Qed.
End snp.

(* ============================== reading the run's stored bytes back ============================== *)
(* 1-byte literal chunks of a region, found by a boolean check (the image-A twin's S00 kit, s10_zs_ok) *)
Definition s20b_c1 (c : YP09.chunk) (off : Z) : option Z :=
match c with
| YP09.mkChunk o (CVal w (SLit z)) =>
  if (Z.eqb o off && N.eqb w 1)%bool then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)) else None
| _ => None
end.
Fixpoint s20b_lit1 (cs : list YP09.chunk) (off : Z) : option Z :=
match cs with
| [] => None
| c :: cs' => match s20b_c1 c off with Some v => Some v | None => s20b_lit1 cs' off end
end.
Fixpoint s20b_zs_b (cs : list YP09.chunk) (off : Z) (l : list Z) : bool :=
match l with
| [] => true
| x :: l' => match s20b_lit1 cs off with Some v => Z.eqb v x && s20b_zs_b cs (off + 1) l' | None => false end
end.
Lemma s20b_lit1_in : forall cs off v, s20b_lit1 cs off = Some v ->
exists z, In (YP09.mkChunk off (CVal 1 (SLit z))) cs /\ v = bv_unsigned (byte_of_word (Z_to_bv 64 z) 0).
Proof.
induction cs as [|c cs IH]; intros off v H; cbn [s20b_lit1] in H; [discriminate H|].
destruct (s20b_c1 c off) as [v'|] eqn:Ec.
- injection H as <-. destruct c as [o cv]. destruct cv as [w e| len | len | d s len]; cbn [s20b_c1] in Ec;
  try discriminate Ec.
  destruct e; try discriminate Ec.
  destruct ((o =? off) && (w =? 1)%N)%bool eqn:Eb; [|discriminate Ec].
  apply andb_prop in Eb as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o w.
  injection Ec as <-. exists z. split; [left; reflexivity | reflexivity].
- destruct (IH off v H) as (z & Hin & Hv). exists z. split; [right; exact Hin | exact Hv].
Qed.
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Lemma s20b_zs_ok : forall E H mem base cs l off,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> s20b_zs_b cs off l = true ->
sa_zs (aview SEGS H mem) (base + off) l.
Proof.
intros E H mem base cs l. induction l as [|x l IH]; intros off Hc Hb i Hi; cbn [length] in Hi; [lia|].
cbn [s20b_zs_b] in Hb. destruct (s20b_lit1 cs off) as [v|] eqn:Ev; [|discriminate Hb].
apply andb_prop in Hb as [Hx Hl]. apply Z.eqb_eq in Hx. subst x.
destruct i as [|i].
- cbn [nth]. destruct (s20b_lit1_in cs off v Ev) as (z & Hin & ->).
  rewrite Forall_forall in Hc. destruct (Hc _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
  rewrite Z.add_0_r in Hb2. unfold aview. rewrite Z.add_0_r, Hb2. reflexivity.
- cbn [nth]. replace (base + off + Z.of_nat (Datatypes.S i)) with ((base + (off + 1)) + Z.of_nat i) by lia.
  apply (IH (off + 1) Hc Hl i). lia.
Qed.
End rd.

(* ======================================= the walk step H i -> A i ======================================= *)
(* the seed of 0x858b0: every register its own atom, the extra atoms 32 = SH(FR) and 33 = ~M; two regions, the
   window [24, 27) at SH(FR) (the probe's three shadow bytes) and the s1 slots 184 (SH(FR)) and 208 (~M), read
   only; the atom ranges that decide the two trap branches: s2 = 256 i in [0, 7936], s4 = i in [0, 31],
   s6 = 32, ~M in [2 ^ 63, 2 ^ 64 - 1] *)
Definition s20b_shr : YP09.region := YP09.mkRegion (Some 32%nat) 24 27 24 27 [].
Definition s20b_s1r : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 216 184 184
    [YP09.mkChunk 184 (CVal 8 (SOff 32 0)); YP09.mkChunk 208 (CVal 8 (SOff 33 0))].
Definition s20b_fa : facts :=
  mkFacts [(18%nat, mkAF 0 7936 0); (20%nat, mkAF 0 31 0); (22%nat, mkAF 32 32 0);
           (33%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0)] [] [].
Definition ss_s20b : sstate := mkSS LO_H sr_atoms [s20b_shr; s20b_s1r] None s20b_fa.


(* ================= piece S20Find: s20_L2, s20_L4 (S11 / S12 piece c): definitions and lemmas outside the sections ================= *)

(* ---- the points of the two segments (offsets from BASE = 0x84dc0; the returns of the jal at 0x858e4, 0x858f4
   and 0x85958; check_absent's two returns are LO_Z and LO_NZ) ---- *)
Definition LO_SLRA : Z := 0xb28.   (* 0x858e8: strlen returned *)
Definition LO_MFRA : Z := 0xb38.   (* 0x858f8: m_find returned (the probe) *)
Definition LO_NMRA : Z := 0xb9c.   (* 0x8595c: m_find returned ("nosuch0") *)

(* ---- the symbolic states ----
   Every register is its own atom; the three extra atoms are 32 = the probe (FR + 192), 33 = c, 34 = m. The one
   region is the s1 slot window [120, 200) read-only, with the three words 120(s1) = probe, 168(s1) = c and
   192(s1) = m as chunks. No instrumented check lies in either segment, so the shadow-entry list is empty and the
   shadow base is a literal. a0 lies in [alo, ahi] (the m_find answer at its return). *)
Definition S20Cx : sv := SLit SHADOW_OFF.
Definition S20Cspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s20c_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 120 200 120 120
    [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 168 (CVal 8 (SOff 33 0));
     YP09.mkChunk 192 (CVal 8 (SOff 34 0))].
Definition s20c_facts (alo ahi : Z) : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (10%nat, mkAF alo ahi 0)] [] [].
Definition s20c_ss (pc alo ahi : Z) : sstate := mkSS pc sr_atoms [s20c_rg] None (s20c_facts alo ahi).


(* ================= piece S20Calloc: the calloc walk kit, s20_L5, s20_S12 (S11 / S12 piece d): definitions and lemmas outside the sections ================= *)

(* ============================== the calloc rule's walk form (generic in segs) ============================== *)
(* the S01 / S02 walk's acalloc04_sub (image B's s12k.v, verbatim): PaCall.v's amalloc04_sub with the calloc rule *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
Variables pc_calloc cstk : Z.
(* a0 = m, a1 = n, the window cstk in place of ASTACK, the zero bytes of the new block in the post *)
Lemma s20d_acalloc04_sub : RtSegCalloc.aseg_calloc04_rule segs B MT pc_calloc cstk ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (m n : Z) (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 m -> getr regsT 11 = w64 n ->
0 <= m -> 0 <= n -> m * n < MALLOC_MAX -> m * n <= YGCalloc.PRIM_MAX -> blocks_bytes Sc + m * n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= cstk -> cstk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT (m * n)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc_calloc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m * n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - cstk) (sp0 + o) (fun a => res <= a < res + req_size (m * n)) /\
(forall i, 0 <= i < m * n -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
mo_le MT Sc S2 (mo_malloc MT (m * n)) /\
ajournal segs B cstk (sp0 + o) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
Proof.
intros AC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k m n o raw ch HJ Ha0 Ha1 Hm Hn Hmn Hprim Hlive Hsp
  Ho16 Ho Hc0 Hstk Hgp Htp Hra Hraw Hnev Hch MOK.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k cstk (sp0 + o) [] o
  HJ eq_refl Ho16 Ho Hc0 Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AC W regsT memT cstk (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 m n 0 raw ch HJ1 Ha0 Ha1 Hm Hn Hmn Hprim
    Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & Hz & MLE).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - cstk) with (sp0 + o - cstk) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact Hz|]. split; [exact MLE|]. replace (0 + 1) with 1 in HJ2 by reflexivity. exact HJ2.
Qed.
End g.
End c.

(* ========================== lists, words, registers (the S01 / S02 walk's s12k.v) ========================== *)
(* blocks_bytes is the sum of the live blocks' sizes *)
Fixpoint s20d_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + s20d_bsum l end.
Lemma s20d_bsum_app : forall l1 l2, s20d_bsum (l1 ++ l2) = s20d_bsum l1 + s20d_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [s20d_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma s20d_bsum_perm : forall l1 l2, Permutation l1 l2 -> s20d_bsum l1 = s20d_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [s20d_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
(* a callee-saved register a call keeps *)
Lemma s20d_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a word every byte of which two readers agree on *)
Lemma s20d_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.

(* cap is the first payload byte mod 40 (SegModel.decode) *)
Lemma s20d_cap_range : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

(* the shadow base (no instrumented check in either run) and the band of the token runner *)
Definition s20d_X : sv := SLit SHADOW_OFF.
Definition s20d_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the seed of s20_L5 at 0x85970: every register its own atom, the slot 56(s1) = cap as a read-only word (atom 32) *)
Definition s20d_rg5 : smem := [YP09.mkRegion (Some 9%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))]].
Definition s20d_ss5 : sstate := mkSS LO_NZ sr_atoms s20d_rg5 None (mkFacts [] [] []).

Section dh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fh.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the s1 slots K85984 / K85994 state lie in [S1 + 16, S1 + 224) *)
Lemma s20d_slots_rng : forall cx c m o v,
  In (o, v) (LT_LC cx c m ++ [(176, shadow_addr (m + seg_spec.MC_N))]) -> 0 <= o <= 216.
Proof.
intros cx c m o v Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- unfold LT_LC in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin.
- destruct Hin as [Hq | []]. injection Hq as <- _. lia.
Qed.
Lemma s20d_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> 0 <= o <= 216) ->
  (forall a, x_s1 cx <= a < x_s1 cx + 224 -> rd' a = rd a) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L HO HK HL o v Hin.
apply (s20d_word_kept rd); [|exact (HL o v Hin)].
intros x Hx. pose proof (HO o v Hin). apply HK. lia.
Qed.
(* NZ's slots without 120(s1) (the probe's address, not read after S11) are K85984's *)
Lemma s20d_slots_sub : forall cx (rd : reader) c m p q,
  lt_slots cx rd (LT_LC cx c m ++ [(120, p); (176, q)]) -> lt_slots cx rd (LT_LC cx c m ++ [(176, q)]).
Proof.
intros cx rd c m p q HL o v Hin. apply HL. apply in_app_or in Hin. apply in_or_app.
destruct Hin as [Hin | Hin]; [left; exact Hin | right; right; exact Hin].
Qed.
(* lt_cm reads only the bytes of c and m *)
Lemma s20d_cm_kept : forall (rd rd' : reader) c m st,
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) ->
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> rd' a = rd a) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st Kc Km Hcm.
unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp in *.
destruct Hcm as ((bc & Hbc & Hec) & (bm & Hbm & Hem)).
split.
- exists bc. split; [|exact Hec]. pose proof (proj1 Hec) as Hl. intros i Hi. rewrite Kc by lia. exact (Hbc i Hi).
- exists bm. split; [|exact Hem]. pose proof (proj1 Hem) as Hl. intros i Hi. rewrite Km by lia. exact (Hbm i Hi).
Qed.

Definition s20d_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s20d_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s20d_E regs extra) n = getr regs r.
Proof.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s20d_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
(* the seed of a stretch with no region and no fact *)
Lemma s20d_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (s20d_E regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s20d_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* the seed of s20_L5, with the 8-byte word at 56(s1) *)
Lemma s20d_seed5 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 cap,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 64 <= 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 56) = Some cap ->
  st_ok_pi SEGS VAL (s20d_E regs [Z_to_bv 64 cap]) s20d_ss5
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_NZ)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 cap R9 Hs1a Hs1b Hcap Hw56.
set (E := s20d_E regs [Z_to_bv 64 cap]).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 cap]) n)
  by (intros n Hn; subst E; unfold s20d_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 56) cap Hw56) as HV8.
unfold s20d_ss5. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20d_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20d_rg5. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s1 56 8 (SOff 32 0) cap);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV8].
- apply pairwise_disjoint_of_extents. unfold s20d_rg5, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. repeat split.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma s20d_nowin_kept : forall E (rs : smem) (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E rs W m m' HF Hro a Ha.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Ha'. unfold windows in Hin. apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hr). apply Z.leb_le in Hro.
injection Heq as Hb Hl Hh. subst. lia.
Qed.

Lemma s20d_blocks_bytes : forall B ly S, blocks_bytes S = s20d_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map s20d_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s20d_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* the image facts' literals carried to a later reader that agrees on their bytes *)
Lemma s20d_lit_kept : forall (B : asyms) (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros B W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
End fh.
End dh.

(* ============================== the segment lemmas (the common Section header, verbatim) ============================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- piece S20Run: s20_L0, s20_L3 (S11 / S12 piece a): lemmas over the listing ---- *)

Lemma s20a_zs_ok : forall E H mem base cs l off,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> s20a_zs_b cs off l = true ->
sa_zs (aview SEGS H mem) (base + off) l.
Proof.
intros E H mem base cs l. induction l as [|x l IH]; intros off Hc Hb i Hi; cbn [length] in Hi; [lia|].
cbn [s20a_zs_b] in Hb. destruct (s20a_lit1 cs off) as [v|] eqn:Ev; [|discriminate Hb].
apply andb_prop in Hb as [Hx Hl]. apply Z.eqb_eq in Hx. subst x.
destruct i as [|i].
- cbn [nth]. destruct (s20a_lit1_in cs off v Ev) as (z & Hin & ->).
  rewrite Forall_forall in Hc. destruct (Hc _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
  rewrite Z.add_0_r in Hb2. unfold aview. rewrite Z.add_0_r, Hb2. reflexivity.
- cbn [nth]. replace (base + off + Z.of_nat (Datatypes.S i)) with ((base + (off + 1)) + Z.of_nat i) by lia.
  apply (IH (off + 1) Hc Hl i). lia.
Qed.


(* ---- piece S20Snp: s20_L1 (S11 / S12 piece b): lemmas over the listing ---- *)

Lemma s20b_seed : forall (W : world SEGS) regs mem s1 sh nm (i : nat),
  getr regs 9 = w64 s1 -> getr regs 18 = w64 (seg_spec.MSEG_SIZE * Z.of_nat i) ->
  getr regs 20 = w64 (Z.of_nat i) -> getr regs 22 = w64 32 -> (i <= 31)%nat ->
  0 <= s1 -> s1 + 216 <= 2 ^ 64 -> 0 <= sh -> sh + 27 <= 2 ^ 64 -> 2 ^ 63 <= nm < 2 ^ 64 ->
  (forall o, 24 <= o < 27 -> writable_at SEGS (mrestrict (w_H W) mem) (sh + o)) ->
  rdword (rdW W mem) (s1 + 184) = Some sh -> rdword (rdW W mem) (s1 + 208) = Some nm ->
  (sh + 27 <= s1 + 184 \/ s1 + 216 <= sh + 24) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) [sh; nm]))) ss_s20b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_H)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 sh nm i R9 R18 R20 R22 Hi H1 H2 Hsh1 Hsh2 Hnm Hwr W184 W208 D1.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [sh; nm]))).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; exact (ew_Eimg_Ereg_nat regs _ n rr Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 sh)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nm)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (V9 : base_val E (Some 9%nat) = s1).
{ cbn [base_val]. rewrite (EE 9%nat 9%bv ltac:(reflexivity)), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (V32 : base_val E (Some 32%nat) = sh) by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_s20b. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, s20b_shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V32. split; [lia|]. split; [lia|]. split; [exact Hwr | apply Forall_nil].
  + unfold region_ok, s20b_s1r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 32 0) sh);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W184)].
    * apply (chunk_ok_val SEGS E _ s1 208 8 (SOff 33 0) nm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W208)].
- apply pairwise_disjoint_of_extents. unfold s20b_shr, s20b_s1r, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s20b_fa f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EE 18%nat 18%bv ltac:(reflexivity)), (EE 20%nat 20%bv ltac:(reflexivity)),
    (EE 22%nat 22%bv ltac:(reflexivity)), E33, R18, R20, R22.
  unfold w64, seg_spec.MSEG_SIZE.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the frame address of a journal's target layout is the entry's *)
Lemma s20b_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.


(* ---- piece S20Find: s20_L2, s20_L4 (S11 / S12 piece c): lemmas over the listing ---- *)

(* ---- the environment of a seed: the registers, then the probe, c and m ---- *)
Definition s20c_E (regs : bvmap 5 word) (p c m : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [p; c; m])).
Lemma s20c_E_reg : forall regs p c m n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s20c_E regs p c m) n = getr regs r.
Proof.
intros regs p c m n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s20c_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma s20c_E_extra : forall regs p c m j, (j < 3)%nat ->
  ew (s20c_E regs p c m) (32 + j) = Z_to_bv 64 (nth j [p; c; m] 0).
Proof.
intros regs p c m j Hj. unfold s20c_E. rewrite Eimg_low by (unfold A_TEXT; cbn; lia).
rewrite ew_Ereg_extra. apply (map_nth (Z_to_bv 64) [p; c; m] 0 j).
Qed.
(* an image atom, as a value rather than as its bv_unsigned *)
Lemma s20c_E_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n).
Proof. intros E n HE Hn. rewrite <- (HE n Hn). rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* a word read through the reader is a 64-bit value *)
Lemma s20c_rdword_rng : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v E. unfold rdword in E.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng _ _ _ _ _ E0). pose proof (sa_aview_rng _ _ _ _ _ E1).
pose proof (sa_aview_rng _ _ _ _ _ E2). pose proof (sa_aview_rng _ _ _ _ _ E3).
pose proof (sa_aview_rng _ _ _ _ _ E4). pose proof (sa_aview_rng _ _ _ _ _ E5).
pose proof (sa_aview_rng _ _ _ _ _ E6). pose proof (sa_aview_rng _ _ _ _ _ E7).
lia.
Qed.
(* an 8-byte chunk of a region, from the word the reader holds there *)
Lemma s20c_chunk8 : forall (W : world SEGS) mem E base off (n : nat) x,
  ew E n = Z_to_bv 64 x -> rdword (rdW W mem) (base + off) = Some x ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E base off n x En Hrd.
pose proof (s20c_rdword_rng _ _ _ _ Hrd) as R.
apply (chunk_ok_val SEGS E _ base off 8 _ x);
  [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R | zside | exact (val_mem_of_rdword SEGS _ _ _ _ Hrd)].
cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the seed at a point of either segment ---- *)
Lemma s20c_seed : forall pc alo ahi (W : world SEGS) (regs : bvmap 5 word) mem s1 p c m,
  getr regs 9 = w64 s1 -> 0x7fff7f800000 <= s1 -> s1 + 200 <= 2 ^ 47 ->
  alo <= bv_unsigned (getr regs 10) <= ahi ->
  rdword (rdW W mem) (s1 + 120) = Some p -> rdword (rdW W mem) (s1 + 168) = Some c ->
  rdword (rdW W mem) (s1 + 192) = Some m ->
  st_ok_pi SEGS VAL (s20c_E regs p c m) (s20c_ss pc alo ahi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S20Cx [] (s20c_E regs p c m) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (s20c_E regs p c m).
Proof.
intros pc alo ahi W regs mem s1 p c m R9 Hs1 Hs1' Ha0 Hp Hc Hm.
set (E := s20c_E regs p c m).
assert (E9 : ew E 9 = w64 s1) by exact (eq_trans (s20c_E_reg regs p c m 9 9%bv eq_refl) R9).
assert (E32 : ew E 32 = Z_to_bv 64 p) by exact (s20c_E_extra regs p c m 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by exact (s20c_E_extra regs p c m 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by exact (s20c_E_extra regs p c m 2 ltac:(lia)).
assert (E10 : ew E 10 = getr regs 10) by exact (s20c_E_reg regs p c m 10 10%bv eq_refl).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
split; [|split; [apply Forall_nil | unfold E, s20c_E; apply Eimg_env]].
unfold s20c_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, s20c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, s20c_rg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + exact (s20c_chunk8 W mem E s1 120 32 p E32 Hp).
  + exact (s20c_chunk8 W mem E s1 168 33 c E33 Hc).
  + exact (s20c_chunk8 W mem E s1 192 34 m E34 Hm).
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [s20c_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, E10, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* a run whose only region has an empty write window changes no byte *)
Lemma s20c_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [s20c_rg] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [s20c_rg] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Hr. cbn [windows map In] in Hin.
destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* ---- the callee-saved registers ---- *)
Lemma s20c_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s20c_pres_eq : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma s20c_pres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H12 H23 z Hz. rewrite (H23 z Hz). exact (H12 z Hz). Qed.
Ltac s20c_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the callee-saved registers a straight-line run of either segment keeps: every one of them is still its own
   atom in the run's symbolic state, so prreg reads it back as the entry's register (the image-A twin's
   s20d_preserved) *)
Ltac s20c_preserved HS EEo :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia);
  repeat (destruct Hc as [-> | Hc]); try subst r;
  lazymatch goal with |- getr _ ?rr = getr _ ?rr =>
    let P := fresh "P" in prreg HS rr P; rewrite P; apply EEo; reflexivity end.

(* ---- sub-range facts of SegABase's shadow and location forms ---- *)
Lemma s20c_addr_le : forall rd q n n', sa_addr rd q n -> 0 <= n' <= n -> sa_addr rd q n'.
Proof.
intros rd q n n' (H0 & H63 & Hm & Hra & Hv) Hn.
split; [exact H0|]. split; [lia|]. split.
- unfold amem_range in *. lia.
- split; [intros x Hx; exact (Hra x ltac:(lia))|].
  intros Hn' s Hs. apply Hv; [lia|]. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (q + n' - 1) (q + n - 1) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (2147450880 + (q + n' - 1) / 8) (2147450880 + (q + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF in *. lia.
Qed.
Lemma s20c_img_le : forall (B : asyms) q n n', sa_img SEGS B q n -> 0 <= n' <= n -> sa_img SEGS B q n'.
Proof. intros B q n n' H Hn x Hx. exact (H x ltac:(lia)). Qed.
Lemma s20c_bytes_app_l : forall rd a l1 l2, sa_bytes rd a (l1 ++ l2) -> sa_bytes rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite <- (app_nth1 l1 l2 ZB0 Hi).
apply H. rewrite length_app. lia.
Qed.
Lemma s20c_zs_kept : forall (rd rd' : reader) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H j Hj. rewrite HK by lia. exact (H j Hj). Qed.
(* the reader form of the entry's C-string premises *)
Lemma s20c_aread : forall (W : world SEGS) regs mem x n stk,
  sa_addr (rdW W mem) x n -> 0 <= n < 2 ^ 32 ->
  (forall a, x <= a < x + n -> rdW W mem a <> None /\ ~ ascratch_stk stk regs a) ->
  aread_ok SEGS stk W regs mem x n.
Proof.
intros W regs mem x n stk (H0 & H63 & Hm & Hra & Hv) Hn Ha.
unfold aread_ok. split; [exact H0|]. split; [exact H63|]. split; [exact Hn|]. split; [exact Ha|].
split; [exact Hm|]. split; [exact Hra | exact Hv].
Qed.
Lemma s20c_zb_len : forall l, Z.of_nat (length (seg_spec.zb l)) = Z.of_nat (length l).
Proof. intros l. unfold seg_spec.zb. rewrite length_map. reflexivity. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* image numbers of the runtime rows (instantiated by the close) *)
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
(* the runtime entries and callees S11 / S12 reach, at every FP state *)
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
(* row 4's image numbers (the image-A twin's text, the S05 walk's, shared by both harness snprintf sites): the
   harness's formats lie in [snp_lo, gotwA) (FR_seg), the read-only ranges inside [snp_lo, snp_hi), and
   [snp_lo, snp_hi) below the allocator ceiling and the fake stack (dest_off_globals for a destination in the
   class-3 frame) *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
(* the walk hypotheses (the close discharges them at image B) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* the image facts: image B's record SegRecBase.seg_img_facts (the kit derives s20_img_relro from its fields), and
   the record of image B's symbols (lib/B/YF0m.v: the stack-protector cells at a later AR state,
   SegRecCells.seg_rec_cells) *)
Hypothesis IMGF : seg_img_facts SEGS B.
Hypothesis HSY : YF0m.SegBSyms B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* ================= piece S20Run: s20_L0, s20_L3 (S11 / S12 piece a) ================= *)

(* the environments of the seeds *)
Definition s20a_EK (regs : bvmap 5 word) (pr shm m n : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [pr; shm; m; m + seg_spec.MC_N; n])).
Definition s20a_EZ (regs : bvmap 5 word) (sh shm mn n : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [sh; shm; mn; n])).

(* the entry sp, the realigned base s1 = (SP0 - 352) & ~31 *)
Lemma s20a_sp : forall cx, lt_base B MT cx ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_sp0 cx - 383 <= x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0.
Proof.
intros cx HBs. pose proof HBs as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 352) 32 ltac:(lia)) as Hm.
split; [lia|]. split; [exact Hal|]. split; [lia|].
rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

(* the class-3 frame of a point: the frame of the state's layout, live in the state, 32-aligned, in the
   application memory, its 64 shadow bytes present, apart from every block *)
Lemma s20a_fr : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o ->
  x_fr cx = frame_addr ly 3 (x_fpos cx) /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  x_fr cx mod 32 = 0 /\ in_app (x_fr cx) 512 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)) /\
  (forall b n, In (b, n) (ablocks B ly S) -> b + req_size n <= x_fr cx \/ x_fr cx + 512 <= b).
Proof.
intros cx ly S W regs mem md k o HF.
destruct HF as (HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : x_fr cx = frame_addr ly 3 (x_fpos cx)).
{ unfold x_fr, frame_addr, LT_FCLS. destruct Hly as (_ & _ & _ & _ & _ & HlF & _). rewrite HlF. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos cx) HAR Hin) as (Hal & Happ & HFp & HSp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos cx) HAR Hin) as (H4096 & Hceil & _).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HSp.
rewrite <- EF in *.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|]. split.
- intros i Hi. exact (proj1 (HSp i Hi)).
- intros b n Hbn. pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n 3 (x_fpos cx) HAR Hbn Hin) as Hd.
  rewrite <- EF in Hd. change (fs_frame_bytes 3) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the seed at K85868 *)
Lemma s20a_seedK : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 pr shm m n,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 224 <= 2 ^ 64 ->
  0 <= pr < 2 ^ 64 -> 0 <= shm -> shm + 1 <= 2 ^ 64 ->
  0 <= m -> m + seg_spec.MC_N + 4 <= 2 ^ 64 -> 0 <= n <= 32 ->
  rdword (rdW W mem) (s1 + 120) = Some pr -> rdword (rdW W mem) (s1 + 176) = Some shm ->
  rdword (rdW W mem) (s1 + 192) = Some m -> rdword (rdW W mem) (s1 + 216) = Some (m + seg_spec.MC_N) ->
  rdW W mem shm = Some 0 -> sa_val (rdW W mem) (m + seg_spec.MC_N) 4 n ->
  (s1 + 224 <= shm \/ shm + 1 <= s1 + 120) ->
  (s1 + 224 <= m + seg_spec.MC_N \/ m + seg_spec.MC_N + 4 <= s1 + 120) ->
  (shm + 1 <= m + seg_spec.MC_N \/ m + seg_spec.MC_N + 4 <= shm) ->
  st_ok_pi SEGS VAL (s20a_EK regs pr shm m n) s20a_ssK
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85868)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 pr shm m n R9 H1 H2 Hpr Hshm1 Hshm2 Hm1 Hm2 Hn W120 W176 W192 W216 Hz Hv D1 D2 D3.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
set (E := s20a_EK regs pr shm m n).
set (X := map (Z_to_bv 64) [pr; shm; m; m + seg_spec.MC_N; n]).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs X) k)
  by (intros k Hk; subst E X; unfold s20a_EK; apply Eimg_low; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
subst X. cbn [Nat.add nth map] in E32, E33, E34, E35, E36. clear EX.
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv0. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv0. }
pose proof (VB 9%nat s1 E9 ltac:(lia)) as V9.
pose proof (VB 33%nat shm E33 ltac:(lia)) as V33.
pose proof (VB 35%nat (m + seg_spec.MC_N) E35 ltac:(lia)) as V35.
destruct (aview_byte SEGS _ _ _ _ Hz) as (bz & Ebz & Ez & _).
assert (HVz : val_mem SEGS (mrestrict (w_H W) mem) (shm + 0) (N.to_nat 1) 0).
{ intros k0 Hk0. assert (k0 = 0%nat) by (cbn in Hk0; lia). subst k0. change (Z.of_nat 0) with 0.
  rewrite !Z.add_0_r. rewrite Ebz. f_equal. apply bv_eq. rewrite <- Ez. reflexivity. }
unfold s20a_ssK. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20a_EK. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20a_rgK. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 120 8 (SOff 32 0) pr);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W120)].
    * apply (chunk_ok_val SEGS E _ s1 176 8 (SOff 33 0) shm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W176)].
    * apply (chunk_ok_val SEGS E _ s1 192 8 (SOff 34 0) m);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W192)].
    * apply (chunk_ok_val SEGS E _ s1 216 8 (SOff 35 0) (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W216)].
  + rewrite V33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ shm 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HVz].
  + rewrite V35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (m + seg_spec.MC_N) 0 4 (SOff 36 0) n);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | cbn; lia | rewrite Z.add_0_r; exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hv)].
- apply pairwise_disjoint_of_extents. unfold s20a_rgK, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V33, V35.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s20a_faK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E36, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the seed at Z i *)
Lemma s20a_seedZ : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 sh shm mn n i,
  getr regs 9 = w64 s1 -> getr regs 20 = w64 i ->
  0 <= s1 -> s1 + 224 <= 2 ^ 64 -> SHADOW_OFF <= sh <= 0x10007fff8000 -> 0 <= shm -> shm + 1 <= 2 ^ 64 ->
  0 <= mn -> mn + 4 <= 2 ^ 64 -> 0 <= n <= 32 -> 0 <= i <= 31 ->
  (forall o, 24 <= o < 27 -> apresent (w_H W) mem (sh + o)) ->
  rdword (rdW W mem) (s1 + 176) = Some shm -> rdword (rdW W mem) (s1 + 184) = Some sh ->
  rdword (rdW W mem) (s1 + 216) = Some mn ->
  rdW W mem shm = Some 0 -> sa_val (rdW W mem) mn 4 n ->
  (sh + 27 <= shm \/ shm + 1 <= sh + 24) -> (sh + 27 <= s1 + 176 \/ s1 + 224 <= sh + 24) ->
  (sh + 27 <= mn \/ mn + 4 <= sh + 24) -> (shm + 1 <= s1 + 176 \/ s1 + 224 <= shm) ->
  (shm + 1 <= mn \/ mn + 4 <= shm) -> (s1 + 224 <= mn \/ mn + 4 <= s1 + 176) ->
  st_ok_pi SEGS VAL (s20a_EZ regs sh shm mn n) s20a_ssZ
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_Z)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 sh shm mn n i R9 R20 H1 H2 Hsh Hshm1 Hshm2 Hmn1 Hmn2 Hn Hi Hpres W176 W184 W216 Hz Hv
  D1 D2 D3 D4 D5 D6.
unfold SHADOW_OFF in Hsh.
set (E := s20a_EZ regs sh shm mn n).
set (X := map (Z_to_bv 64) [sh; shm; mn; n]).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs X) k)
  by (intros k Hk; subst E X; unfold s20a_EZ; apply Eimg_low; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 i)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
subst X. cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv0. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv0. }
pose proof (VB 9%nat s1 E9 ltac:(lia)) as V9.
pose proof (VB 32%nat sh E32 ltac:(lia)) as V32.
pose proof (VB 33%nat shm E33 ltac:(lia)) as V33.
pose proof (VB 34%nat mn E34 ltac:(lia)) as V34.
destruct (aview_byte SEGS _ _ _ _ Hz) as (bz & Ebz & Ez & _).
assert (HVz : val_mem SEGS (mrestrict (w_H W) mem) (shm + 0) (N.to_nat 1) 0).
{ intros k0 Hk0. assert (k0 = 0%nat) by (cbn in Hk0; lia). subst k0. change (Z.of_nat 0) with 0.
  rewrite !Z.add_0_r. rewrite Ebz. f_equal. apply bv_eq. rewrite <- Ez. reflexivity. }
unfold s20a_ssZ. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20a_EZ. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20a_rgZ. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite V32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite V33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ shm 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HVz].
  + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 176 8 (SOff 33 0) shm);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W176)].
    * apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 32 0) sh);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W184)].
    * apply (chunk_ok_val SEGS E _ s1 216 8 (SOff 34 0) mn);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W216)].
  + rewrite V34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mn 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | cbn; lia | rewrite Z.add_0_r; exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hv)].
- apply pairwise_disjoint_of_extents. unfold s20a_rgZ, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V32, V33, V34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s20a_faZ f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E32, E35, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the probe's three shadow bytes (offsets 24 .. 26 of the frame's 36) *)
Lemma s20a_zs_probe : forall rd sh o, sa_zs rd sh (lt_fsh o) ->
  sa_zs rd (sh + 24) (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]).
Proof.
intros rd sh o H i Hi.
replace (sh + 24 + Z.of_nat i) with (sh + Z.of_nat (24 + i)) by lia.
assert (Hi3 : (i < 3)%nat) by (destruct (fo_probe o); cbn [length] in Hi; lia).
rewrite (H (24 + i)%nat) by (rewrite lt_fsh_len; lia).
f_equal. destruct o as [[] [] [] [] []]; cbn [fo_probe];
  (do 3 (destruct i as [|i]; [reflexivity|])); lia.
Qed.

(* memory kept by a run whose regions have no write window *)
Ltac s20a_keep0 K :=
  lazymatch goal with Hfr : frame_of ?E0 _ (mrestrict (w_H ?W0) ?m0) (mrestrict _ (ms_mem ?ms0)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> rdW W0 (ms_mem ms0) a = rdW W0 m0 a);
  [ intros a Ha; apply (kept_of_frame E0 _ (w_H W0) m0 (ms_mem ms0) (fun _ => False) Hfr); [| exact Ha | tauto];
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia |]);
    destruct Hin
  | clear Hfr; try lazymatch goal with HF0 : frame_of E0 _ m0 (ms_mem ms0) |- _ => clear HF0 end;
    try lazymatch goal with HG0 : mem_grows (mrestrict _ m0) _ |- _ => clear HG0 end ] end.

(* memory kept by a run of Z i: only the probe's three shadow bytes SH(FR) + 24 .. 26 (the window of atom 32) *)
Ltac s20a_keepZ U K :=
  lazymatch type of U with bv_unsigned (ew _ _) = ?sh =>
  lazymatch goal with Hfr : frame_of ?E0 _ (mrestrict (w_H ?W0) ?m0) (mrestrict _ (ms_mem ?ms0)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 24 <= a < sh + 27) -> rdW W0 (ms_mem ms0) a = rdW W0 m0 a);
  [ intros a Ha Hna;
    apply (kept_of_frame E0 _ (w_H W0) m0 (ms_mem ms0) (fun y => sh + 24 <= y < sh + 27) Hfr);
    [| exact Ha | exact Hna];
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hx; rewrite ?U in Hx;
      cbv beta; lia |]);
    destruct Hin
  | clear Hfr; try lazymatch goal with HF0 : frame_of E0 _ m0 (ms_mem ms0) |- _ => clear HF0 end;
    try lazymatch goal with HG0 : mem_grows (mrestrict _ m0) _ |- _ => clear HG0 end ] end end.

(* the write permission of a run of Z i: the window SH(FR) + 24 .. 26 (atom 32, U : its value) lies in the shadow
   of the class-3 frame the journal owns *)
Ltac s20a_awrZ U EFR cx :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_gen; [reflexivity | exact U | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 3, (x_fpos cx);
    split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
    change (fs_frame_bytes 3 / 8) with 64; rewrite <- EFR;
    change (shadow_addr (x_fr cx)) with (x_sh cx); lia
  | repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil ].

(* the probe's three shadow bytes after a run of Z i: f8 f8 f8, read back from the literal chunks of region 0 *)
Ltac s20a_zsZ HS U HZ :=
  lazymatch type of U with bv_unsigned (ew ?E0 _) = ?sh =>
  lazymatch type of HS with st_ok_pi _ _ _ ?ssB (restrict (w_H ?W0) ?msB) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  let RSH := fresh "RSH" in let CSH := fresh "CSH" in
  assert (RSH : region_ok SEGS E0 (mrestrict (w_H W0) (ms_mem msB)) r0)
    by exact (st_ok_pi_region_nth E0 ssB (restrict (w_H W0) msB) 0%nat r0 HS ltac:(vm_compute; reflexivity));
  destruct RSH as (_ & _ & _ & CSH);
  cbn [YP09.r_base YP09.r_chunks base_val] in CSH; rewrite U in CSH;
  pose proof (s20a_zs_ok E0 (w_H W0) (ms_mem msB) sh _ [0xf8; 0xf8; 0xf8] 24 CSH ltac:(vm_compute; reflexivity))
    as HZ;
  clear CSH end end.

Lemma s20_L0 : S20A_H B MT 0 -> S20A_N B MT -> LT_K85868_stmt B MT.
Proof.
intros HH HN. unfold LT_K85868_stmt.
intros cx ly S W regs mem md k acc c m HBs Hfrm HCORE HC HM HSL HCM.
assert (HCTX : s20_ctx B MT cx ly S W regs mem md k acc LFO0 c m)
  by (split; [exact HCORE | split; [exact HC | split; [exact HM | split; [exact HSL | exact HCM]]]]).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFLW & H200 & HSH & H184).
pose proof (s20a_sp cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32).
pose proof (s20a_fr cx ly S W regs mem md k LFO0 HFR) as (EFR & HF4 & HFc & HF32 & HFapp & HFsh & HFsep).
pose proof HJ as (HAR & _).
pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & Hmapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite HRM in Hmc, Hmapp.
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
assert (W120 : rdword (rdW W mem) (x_s1 cx + 120) = Some (x_fr cx + FO_PROBE))
  by (apply HSL; apply in_or_app; right; left; reflexivity).
assert (W176 : rdword (rdW W mem) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HSL; apply in_or_app; right; right; left; reflexivity).
assert (W192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m)
  by (apply HSL; apply in_or_app; left; cbn [LT_LC In]; repeat (first [left; reflexivity | right])).
assert (W216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HSL; apply in_or_app; left; cbn [LT_LC In]; repeat (first [left; reflexivity | right])).
pose proof HCM as (_ & HMC).
assert (HN0 : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eauto).
destruct HN0 as (Hnv & Hn32).
assert (Hz : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0) by (eapply s20_mn_shadow; eauto).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (subst n; lia).
(* the shadow addresses of m + 0x2000 and of FR, without division *)
pose proof (Z.div_mod (m + seg_spec.MC_N) 8 ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound (m + seg_spec.MC_N) 8 ltac:(lia)) as Mm.
assert (Hshm : shadow_addr (m + seg_spec.MC_N) = SHADOW_OFF + (m + seg_spec.MC_N) / 8) by reflexivity.
set (qm := (m + seg_spec.MC_N) / 8) in *.
pose proof (Z.div_mod (x_fr cx) 8 ltac:(lia)) as DF.
assert (HF8 : x_fr cx mod 8 = 0).
{ destruct (Z.mod_divide (x_fr cx) 32 ltac:(lia)) as [Hd _]. destruct (Hd HF32) as [q Hq].
  rewrite Hq. replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hxsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
set (qF := x_fr cx / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
unfold FO_PROBE in W120.
pose proof (s20a_seedK W regs mem (x_s1 cx) (x_fr cx + 192) (shadow_addr (m + seg_spec.MC_N)) m n
  R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hn
  W120 W176 W192 W216 Hz Hnv ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (SHOK : sh_ok SEGS s20a_X [] (s20a_EK regs (x_fr cx + 192) (shadow_addr (m + seg_spec.MC_N)) m n)
  (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20a_EK regs (x_fr cx + 192) (shadow_addr (m + seg_spec.MC_N)) m n))
  by (unfold s20a_EK; apply Eimg_env).
remember (s20a_EK regs (x_fr cx + 192) (shadow_addr (m + seg_spec.MC_N)) m n) as E eqn:HE.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs r)
  by (intros k0 r Hk; rewrite HE; unfold s20a_EK; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [x_fr cx + 192; shadow_addr (m + seg_spec.MC_N); m; m + seg_spec.MC_N; n])
    (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; unfold s20a_EK; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth map] in E32, E33, E34, E35, E36. clear EX HE.
unfold cfg_at. change (w64 (BASE + LO_K85868)) with (Z_to_bv 64 (BASE + LO_K85868)).
(* 0x85868 .. 0x8587c: check 24 (SH(m + 0x2000) from 176(s1), its shadow byte 0: bnez falls through),
   a0 := m->n; the run stops at blez a0 *)
paj_run_tok RUN HS HJ SHOK s20a_span.
{ awr_ok_tac. }
s20a_keep0 K1.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
assert (HZ0 : sa_zs (rdW W mem) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]) by exact (s20a_zs_probe _ _ LFO0 HSH).
psrr_branch_tok RUN BR HS SHOK s20a_span.
- (* blez taken: m->n = 0, no turn; 0x8587c jumps to 0x85948 (N) *)
  assert (Hn0 : n <= 0).
  { cbn [branch_taken sv_denot] in Hc. rewrite E36, Z.add_0_r, (unsigned_lit_small n) in Hc by lia.
    rewrite bv_lts_small in Hc by lia. destruct (Z.ltb_spec 0 n); [discriminate Hc | lia]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20a_span LO_N.
  { awr_ok_tac. }
  s20a_keep0 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha _; rewrite K2, K1 by exact Ha; reflexivity).
  assert (HZ1 : sa_zs (rdW W (ms_mem ms)) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]).
  { intros i Hi. cbn [length] in Hi. rewrite K2, K1 by lia. exact (HZ0 i Hi). }
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  exact (HN fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm HCTX2).
- (* blez not taken: 0 < m->n; 0x85880 .. 0x858ac, the loop's registers, to H 0 at 0x858b0 *)
  assert (Hn0 : 0 < n).
  { cbn [branch_taken sv_denot] in Hc. rewrite E36, Z.add_0_r, (unsigned_lit_small n) in Hc by lia.
    rewrite bv_lts_small in Hc by lia. destruct (Z.ltb_spec 0 n); [lia | discriminate Hc]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20a_span LO_H.
  { awr_ok_tac. }
  s20a_keep0 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha _; rewrite K2, K1 by exact Ha; reflexivity).
  assert (HZ1 : sa_zs (rdW W (ms_mem ms)) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]).
  { intros i Hi. cbn [length] in Hi. rewrite K2, K1 by lia. exact (HZ0 i Hi). }
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  assert (Hlt : (0 < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold n in Hn0; lia).
  assert (HLR : s20_lregs cx (ms_regs ms) m 0).
  { unfold s20_lregs.
    split; [rewrite P18; reflexivity|].
    split; [rewrite P19; change (ew E 248) with (ew E (A_OBJ 7)); apply bv_eq;
      rewrite (HEI (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); unfold w64;
      rewrite unsigned_lit_small by exact (pa_val_range (A_OBJ 7)); reflexivity|].
    split; [rewrite P20; reflexivity|].
    split; [rewrite P21; reflexivity|].
    split; [rewrite P22; reflexivity|].
    split; [rewrite P23; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite P25, E34; reflexivity|].
    rewrite P26, E32; reflexivity. }
  exact (HH fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm Hlt HCTX2 HLR).
Qed.

Lemma s20_L3 : forall i, S20A_H B MT (Datatypes.S i) -> S20A_N B MT -> S20_Z_stmt B MT i.
Proof.
intros i HH HN. unfold S20_Z_stmt.
intros cx ly S W regs mem md k acc c m HBs Hfrm Hlt HCTX HLR HPZ.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFLW & H200 & HSH & H184).
pose proof HLR as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof (s20a_sp cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32).
pose proof (s20a_fr cx ly S W regs mem md k LFO_P HFR) as (EFR & HF4 & HFc & HF32 & HFapp & HFsh & HFsep).
pose proof HJ as (HAR & _).
pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & Hmapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite HRM in Hmc, Hmapp.
pose proof (HFsep m seg_spec.SEG_M_SIZE HMin) as HmF. rewrite HRM in HmF.
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
assert (W176 : rdword (rdW W mem) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HSL; apply in_or_app; right; right; left; reflexivity).
assert (W216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HSL; apply in_or_app; left; cbn [LT_LC In]; repeat (first [left; reflexivity | right])).
pose proof HCM as (_ & HMC).
assert (HN0 : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eauto).
destruct HN0 as (Hnv & Hn32).
assert (Hz : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0) by (eapply s20_mn_shadow; eauto).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (subst n; lia).
assert (Hilt : Z.of_nat i < n) by (subst n; lia).
(* the shadow addresses of m + 0x2000 and of FR, without division *)
pose proof (Z.div_mod (m + seg_spec.MC_N) 8 ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound (m + seg_spec.MC_N) 8 ltac:(lia)) as Mm.
assert (Hshm : shadow_addr (m + seg_spec.MC_N) = SHADOW_OFF + (m + seg_spec.MC_N) / 8) by reflexivity.
set (qm := (m + seg_spec.MC_N) / 8) in *.
pose proof (Z.div_mod (x_fr cx) 8 ltac:(lia)) as DF.
assert (HF8 : x_fr cx mod 8 = 0).
{ destruct (Z.mod_divide (x_fr cx) 32 ltac:(lia)) as [Hd _]. destruct (Hd HF32) as [q Hq].
  rewrite Hq. replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hxsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
set (qF := x_fr cx / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
pose proof (s20a_seedZ W regs mem (x_s1 cx) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) n
  (Z.of_nat i) R9 R20 ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) Hn ltac:(lia) (fun o Ho => HFsh o ltac:(lia)) W176 H184 W216 Hz Hnv
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS0.
(* s7 = -8 as a literal, so that the three stores leave literal chunks *)
pose proof (st_ok_pi_pin_reg' _ _ _ 23%bv (-8) HS0 R23 eq_refl) as HS. clear HS0.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (SHOK : sh_ok SEGS s20a_X []
  (s20a_EZ regs (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) n) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20a_EZ regs (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) n))
  by (unfold s20a_EZ; apply Eimg_env).
remember (s20a_EZ regs (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) n) as E eqn:HE.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs r)
  by (intros k0 r Hk; rewrite HE; unfold s20a_EZ; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [x_sh cx; shadow_addr (m + seg_spec.MC_N); m + seg_spec.MC_N; n]) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; unfold s20a_EZ; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX HE.
assert (U32 : bv_unsigned (ew E 32) = x_sh cx) by (rewrite E32; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + LO_Z)) with (Z_to_bv 64 (BASE + LO_Z)).
(* 0x85908 .. 0x85934: the probe out of scope (three 0xf8 shadow bytes through 184(s1)), check 25 (its shadow
   byte 0: bnez falls through), a0 := m->n, s4 := i + 1, s2 := 256 (i + 1); the run stops at blt s4,a0 *)
paj_run_tok RUN HS HJ SHOK s20a_spanZ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, (x_fpos cx).
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes 3 / 8) with 64. rewrite <- EFR.
    change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
s20a_keepZ U32 K1.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s20a_spanZ.
- (* blt taken: i + 1 < m->n; to H (i + 1) at 0x858b0 *)
  assert (Hc1 : Z.of_nat i + 1 < n).
  { cbn [branch_taken sv_denot] in Hc.
    rewrite (EE 20%nat 20%bv eq_refl), R20, E35, Z.add_0_r in Hc. unfold w64 in Hc.
    rewrite (unsigned_lit_small (Z.of_nat i)), (unsigned_lit_small n) in Hc by lia.
    rewrite bv_lts_small in Hc by lia. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20a_spanZ LO_H.
  { s20a_awrZ U32 EFR cx. }
  s20a_keepZ U32 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  s20a_zsZ HS U32 HZ1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (K2 a Ha Hna), (K1 a Ha Hna); reflexivity).
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  assert (Hlt2 : (Datatypes.S i < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold n in Hc1; lia).
  assert (HLR2 : s20_lregs cx (ms_regs ms) m (Datatypes.S i)).
  { unfold s20_lregs.
    split.
    { rewrite P18, (EE 18%nat 18%bv eq_refl), R18. unfold w64.
      rewrite unsigned_lit_small by (unfold seg_spec.MSEG_SIZE; lia).
      f_equal. unfold seg_spec.MSEG_SIZE. lia. }
    split; [rewrite P19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split.
    { rewrite P20, (EE 20%nat 20%bv eq_refl), R20. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia. }
    split; [rewrite P21, (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P22, (EE 22%nat 22%bv eq_refl); exact R22|].
    split; [rewrite P23; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite P25, (EE 25%nat 25%bv eq_refl); exact R25|].
    rewrite P26, (EE 26%nat 26%bv eq_refl); exact R26. }
  exact (HH fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm Hlt2 HCTX2 HLR2).
- (* blt not taken: m->n <= i + 1; j 0x85948 (N) *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20a_spanZ LO_N.
  { s20a_awrZ U32 EFR cx. }
  s20a_keepZ U32 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  s20a_zsZ HS U32 HZ1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (K2 a Ha Hna), (K1 a Ha Hna); reflexivity).
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  exact (HN fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm HCTX2).
Qed.


(* ================= piece S20Snp: s20_L1 (S11 / S12 piece b) ================= *)

(* the entry sp and the realigned base S1 = (SP0 - 352) & ~31 *)
Lemma s20b_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* the class-3 frame of a state the journal reaches: its address, its place in the fake stack (above the image and
   row 4's snp_hi), its bytes and its 64 shadow bytes present and not the runtime's *)
Lemma s20b_frame_at : forall cx ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\ In (LT_FCLS, x_fpos cx) (frames S) /\
  snp_hi <= ly_F ly /\ ly_F ly <= x_fr cx /\ kImgEnd <= ly_F ly /\ 4096 <= x_fr cx /\
  x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (forall j, 0 <= j < 64 -> apresent (w_H W) mem (x_sh cx + j) /\ ~ aowned B ly S (x_sh cx + j)).
Proof.
intros cx ly S W mem md k HJ.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20b_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : x_fr cx = ly_F ly + fs_frame_off LT_FCLS (x_fpos cx)) by (rewrite <- EF; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (_ & Happ & Hpres & Hspres).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (H4096 & Hceil & _).
destruct (frame_facts B ly S _ LT_FCLS (x_fpos cx) (proj1 HAR) HinF) as (Hc & Hp & HFapp & HNO & _ & Hoff & _).
destruct (pa_img_cover ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
pose proof (HSNP_FAKE ly S W mem md HAR) as HFK.
assert (F512 : fs_frame_bytes LT_FCLS = 512) by reflexivity.
rewrite EF, F512 in Happ, Hpres, Hceil. rewrite EF in H4096. rewrite EF, F512 in Hspres.
change (512 / 8) with 64 in Hspres.
unfold kFakeFramesOff, LT_FCLS in Hoff.
assert (HFimg : kImgEnd <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) kImgEnd) as [Hlt|Hge]; [exfalso|exact Hge].
  apply HNO. exists (Z.max (ly_F ly) 0x10000). unfold in_zr. cbn [fst snd].
  destruct HFapp as [HF1 _]. unfold kFakeStackSize, kImgEnd in *. split; [lia | left; lia]. }
split; [exact EF|]. split; [exact HinF|]. split; [exact HFK|].
split; [unfold LT_FCLS in EF2; lia|]. split; [exact HFimg|]. split; [exact H4096|]. split; [exact Hceil|].
split; [exact Happ|]. split; [exact Hpres|]. unfold x_sh. exact Hspres.
Qed.

(* m->seg[i].name through the reader of a state where m is a harness block holding the model state mc: a C string
   of at most 15 bytes inside m's entry i, its slack word mapped, addressable, 8 bytes past its NUL in application
   memory *)
Lemma s20b_name : forall ly S (W : world SEGS) mem md m mc i,
  AR SEGS B ly S W mem md -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  sa_mconf (rdW W mem) m mc -> (i < length (SegModel.mc_seg mc))%nat ->
  0 < seg_spec.mseg_addr m i /\ m <= seg_spec.mseg_addr m i /\
  seg_spec.mseg_addr m i + 256 <= m + seg_spec.SEG_M_SIZE /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) < 16)%nat /\
  sa_str (rdW W mem) (seg_spec.mseg_addr m i) (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) /\
  sa_addr (rdW W mem) (seg_spec.mseg_addr m i)
    (Z.of_nat (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d))) + 1) /\
  amem_range (seg_spec.mseg_addr m i)
    (Z.of_nat (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d))) + 8).
Proof.
intros ly S W mem md m mc i HAR Hhb Hmc Hi.
destruct Hhb as (Hin & H4096 & H16 & _).
pose proof asan_consts as (C1 & _).
assert (Hn32 : (length (SegModel.mc_seg mc) <= 32)%nat) by (eapply proj2; eapply s20_mconf_n; eassumption).
set (nm := SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)).
assert (HNM : sa_zs (rdW W mem) (seg_spec.mseg_addr m i) (nm ++ [0]) /\ ~ In 0 nm /\ (length nm < 16)%nat /\
  (forall j, 0 <= j < 16 -> rdW W mem (seg_spec.mseg_addr m i + j) <> None))
  by (eapply s20_mconf_name; eassumption).
destruct HNM as (Hzs & Hn0 & Hl16 & Hmap).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreq].
pose proof (al_blocks _ _ LAWS ly S W mem md m _ HAR Hin) as (_ & _ & Hceil & _).
assert (Ew : seg_spec.mseg_addr m i = m + 256 * Z.of_nat i) by reflexivity.
assert (Hw8 : exists q, seg_spec.mseg_addr m i = 8 * q).
{ exists (2 * (m / 16) + 32 * Z.of_nat i). rewrite Ew. pose proof (Z.div_mod m 16 ltac:(lia)). lia. }
destruct Hw8 as (q & Hq).
assert (Hlim : seg_spec.mseg_addr m i + 256 <= m + seg_spec.SEG_M_SIZE)
  by (rewrite Ew; unfold seg_spec.SEG_M_SIZE; lia).
split; [lia|]. split; [lia|]. split; [exact Hlim|]. split; [exact Hl16|].
split.
{ split; [split; [exact Hzs | exact Hn0]|].
  intros x Hx.
  pose proof (Z.div_mod (seg_spec.mseg_addr m i + Z.of_nat (length nm)) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (seg_spec.mseg_addr m i + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
  assert (Hj : 0 <= x - seg_spec.mseg_addr m i < 16) by lia.
  pose proof (Hmap _ Hj) as Hx'.
  replace (seg_spec.mseg_addr m i + (x - seg_spec.mseg_addr m i)) with x in Hx' by lia.
  exact Hx'. }
split.
{ split; [lia|]. split; [lia|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia]|].
  intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia | lia]. }
apply (amem_range_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE); [exact HAR | exact Hin | lia | lia].
Qed.

(* ---- H i -> A i: the probe in scope, the two trap branches not taken, a1 = 18, a0 = the probe, a2 = "%sx",
   a3 = &m->seg[i].name, snprintf ---- *)
Lemma s20_L1 : forall i, S20A_A B MT i -> S20_H_stmt B MT i.
Proof.
intros i HAA. unfold S20_H_stmt.
intros cx ly S W regs mem md k acc c m HB Hfrm Hlt Hctx HL.
pose proof Hctx as (HC & _ & HHm & HSL & HCM).
pose proof HC as (HF & _ & _ & _).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & _ & _ & W184).
pose proof HL as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (s20b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HFM : LTOI_FRAME_MAX = 368) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s20b_frame_at cx ly S W mem md k HJ) as (EF0 & _ & _ & _ & _ & HF4096 & HFceil & _ & _ & HSP0).
(* the loop index (i < m->n <= 32) and m's block below 2 ^ 63 (lt_hblk's sa_addr): the two traps' ranges *)
pose proof (proj2 HCM) as HMC.
assert (Hn32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply proj2; eapply s20_mconf_n; eassumption).
assert (Hi31 : (i <= 31)%nat) by lia.
pose proof HHm as (_ & Hm4 & _ & (_ & Hm63 & _)).
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite HMS in Hm63.
assert (W208 : rdword (rdW W mem) (x_s1 cx + 208) = Some (lt_not m))
  by (apply HSL; apply in_or_app; left; cbn [LT_LC In]; repeat (first [left; reflexivity | right])).
(* the seed: SH(FR) and ~M from the s1 slots 184 and 208, s5 pinned to 2 *)
pose proof (s20b_seed W regs mem (x_s1 cx) (x_sh cx) (lt_not m) i R9 R18 R20 R22 Hi31) as HS0.
specialize (HS0 ltac:(lia) ltac:(lia) ltac:(unfold x_sh, shadow_addr, SHADOW_OFF; lia)
  ltac:(unfold x_sh, shadow_addr, SHADOW_OFF; lia) ltac:(unfold lt_not; lia)).
specialize (HS0 ltac:(intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HSP0 o ltac:(lia)))) W184 W208).
specialize (HS0 ltac:(left; unfold x_sh, shadow_addr, SHADOW_OFF; lia)).
pose proof (st_ok_pi_pin_reg' _ _ _ 21%bv 2 HS0 R21 eq_refl) as HS. clear HS0.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) [x_sh cx; lt_not m]))) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; exact (ew_Eimg_Ereg_nat regs _ n rr Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 (x_sh cx))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = x_sh cx)
  by (rewrite E32; apply unsigned_lit_small; unfold x_sh, shadow_addr, SHADOW_OFF; lia).
clearbody E.
unfold cfg_at, w64.
(* 0x858b0 .. 0x858dc: SH(FR) from 184(s1), the probe's three shadow bytes 00 00 02, beq s4,s6 not taken (s4 in
   [0, 31], s6 = 32), ~M from 208(s1), bltu a0,s2 not taken (~M >= 2 ^ 63 > 7936 >= s2), a3 := s9 + s2,
   a1 := 18, a0 := s10, a2 := s3, jal snprintf *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 32%nat) (b := x_sh cx); [reflexivity | exact U32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
    rewrite EF0. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
(* the stored bytes: the region's chunks at the call *)
lazymatch type of HS with st_ok _ _ ?ssB _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth _ ssB _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as RSH end.
destruct RSH as (_ & _ & _ & CSH).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH. rewrite U32 in CSH.
pose proof (s20b_zs_ok _ (w_H W) _ (x_sh cx) _ [0; 0; 2] 24 CSH ltac:(vm_compute; reflexivity)) as HZS.
(* the registers at the call *)
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
(* a3 = s2 + s9 = 256 i + m = &m->seg[i].name (the add 0x858cc) *)
assert (A13 : getr (ms_regs ms) 13 = w64 (seg_spec.mseg_addr m i)).
{ rewrite P13, (EEo 18%nat 18%bv ltac:(reflexivity)), (EEo 25%nat 25%bv ltac:(reflexivity)), R18, R25.
  unfold w64. rewrite YI08.alu64_add_lit. f_equal. unfold seg_spec.mseg_addr. lia. }
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; first [apply EEo; reflexivity | rewrite R21; reflexivity] | ]).
  destruct Hr. }
pmkst HS.
(* the memory after the run: only the three shadow bytes changed *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W) mem (ms_mem ms) (fun y => x_sh cx + 24 <= y < x_sh cx + 27) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
    change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?U32 in Hx; cbv beta; lia |]).
  destruct Hin. }
assert (RK1 : s20_rkept regs (ms_regs ms)).
{ split; [apply KR; cbn; tauto|]. split; [apply KR; cbn; tauto|]. split; [apply KR; cbn; tauto|].
  split; [apply KR; cbn; tauto | apply KR; cbn; tauto]. }
(* s20_ctx with the probe in scope *)
assert (Hctx1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m).
{ eapply s20_ctx_store; try eassumption; first [exact RK1 | exact KEEP | reflexivity | exact HZS]. }
pose proof Hctx1 as (HC1 & HHc1 & HHm1 & HSL1 & HCM1).
pose proof HC1 as (HF1 & HI1 & HBL1 & HBUD1).
pose proof (proj1 HJ) as HAR1.
pose proof (s20b_frame_at cx ly S W (ms_mem ms) md1 k HJ)
  as (EF & HinF & HFK & HFF & HFimg & HF4096' & HFceil' & HFapp & HFpres & _).
assert (HPA : sa_addr (rdW W (ms_mem ms)) (s20_probe cx) 18).
{ eapply s20_probe_addr; first [exact HF1 | reflexivity | eassumption]. }
pose proof (s20b_name ly S W (ms_mem ms) md1 m (x_mcF cx) i HAR1 HHm1 (proj2 HCM1) Hlt)
  as (Hw0 & Hwm & Hwlim & Hnl & Hstr & Hwaddr & Hwamem).
pose proof (al_blocks _ _ LAWS ly S W (ms_mem ms) md1 m seg_spec.SEG_M_SIZE HAR1 (proj1 HHm1))
  as (_ & _ & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS ly S W (ms_mem ms) md1 m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR1
  (proj1 HHm1) HinF) as Hsep.
rewrite EF in Hsep. change (fs_frame_bytes LT_FCLS) with 512 in Hsep.
(* the image facts at the call: the format, the stack-protector cells, the read-only view *)
destruct HI1 as (HRO & HIM & _).
destruct HIM as (_ & _ & Hfz & _ & _ & _ & _ & _ & Hssp & _).
assert (HLIT : In LIT_PROBE LTOI_FZ_LITS)
  by (unfold LTOI_FZ_LITS; apply in_or_app; left; unfold LTOI_LITS; cbn [In]; tauto).
destruct (Hfz LIT_PROBE HLIT) as ((Hf0 & ((Hfzs & _) & _) & Hpin & _) & _).
pose proof (Hpin ly S W (ms_mem ms) md1 HAR1) as Hfaddr.
destruct (HSNP_LIT LIT_PROBE ltac:(unfold LTOI_LITS; cbn [In]; tauto)) as [Hflo Hfhi].
assert (EF7 : VAL (A_OBJ 7) = seg_litA_fz LIT_PROBE).
{ rewrite (VOBJS 7%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
assert (ELP : LIT_PROBE = [37; 115; 120]) by (vm_compute; reflexivity).
assert (HROM : RtDefs.rt_rom_view SEGS B W (ms_mem ms)).
{ intros a Ha Ho He. apply HRO; [left; exact Ha | exact Ho | exact He]. }
(* the text: the name and 'x', at most 16 bytes, so all of it and its NUL are written *)
assert (HTlen : (length (s20_T cx i) <= 16)%nat)
  by (unfold s20_T; rewrite length_app; cbn [length]; unfold x_seg; lia).
assert (Esb : RtPFShared.sn_bytes (18 - 1) (s20_T cx i) = s20_T cx i ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity|]. change (Z.to_nat (18 - 1)) with 17%nat. lia. }
assert (Esl : RtPFShared.sn_len (18 - 1) (s20_T cx i) = Z.of_nat (length (s20_T cx i)) + 1).
{ unfold RtPFShared.sn_len. rewrite Esb, length_app. cbn [length]. lia. }
assert (Hpr : s20_probe cx = x_fr cx + 192) by reflexivity.
assert (Usp : spZ (ms_regs ms) = x_s1 cx).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
eapply SRr_bind.
{ apply (s20b_aj_snprintf_atSF SEGS B LAWS pa_segs_low snp_lo snp_hi snp_cr _ gotwA guardA (ASNPRINTF fx)
    W (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md1 k (s20_probe cx) 18 (VAL (A_OBJ 7)) LIT_PROBE
    [RtPFSeg.PRel RtPFPf.Ps; RtPFSeg.PRel (RtPFPf.PLit 120)] (seg_spec.mseg_addr m i)
    (SegModel.ms_name (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d))
    (s20_T cx i) (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + LO_A)) HJ).
  - rewrite P10, (EEo 26%nat 26%bv ltac:(reflexivity)). exact R26.
  - rewrite P11. reflexivity.
  - rewrite P12, (EEo 19%nat 19%bv ltac:(reflexivity)). exact R19.
  - exact A13.
  - lia.
  - rewrite Hpr. lia.
  - rewrite Usp. lia.
  - pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)). pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)).
    apply Z.mod_divide; [lia|]. exists (2 * (x_s1 cx / 32) - x_sp0 cx / 16). lia.
  - lia.
  - unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - lia.
  - rewrite (KR 3%bv ltac:(cbn; tauto)), R3. exact Hgp0.
  - rewrite (KR 4%bv ltac:(cbn; tauto)), R4. exact Htp0.
  - exact P1.
  - apply ret_ok_codeptr_v; [unfold LO_A; lia | reflexivity].
  - intros a Ha. rewrite Hpr in Ha.
    destruct (HFpres a ltac:(lia)) as [Hap Hno].
    split; [|split; [exact (apresent_writable SEGS _ _ _ Hap) | exact Hno]].
    right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left.
    rewrite EF. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS) with 512. lia.
  - rewrite Hpr. unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - exact HPA.
  - rewrite Hpr. destruct HFapp as [HA1 [HA2 | [HA3 HA4]]];
      unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
  - unfold zdisjoint. cbn [fst snd]. rewrite Hpr. right. lia.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HSNP_CR r Hr) as (H1 & H2 & H3).
    rewrite Hpr. lia.
  - exact Hssp.
  - unfold gotwA. lia.
  - rewrite Hpr. unfold gotwA, kImgEnd in *. lia.
  - unfold guardA. lia.
  - rewrite Hpr. unfold guardA, kImgEnd in *. lia.
  - exact HROM.
  - rewrite EF7. exact Hf0.
  - rewrite EF7. exact Hfzs.
  - rewrite EF7. exact Hfaddr.
  - rewrite EF7. exact Hflo.
  - rewrite EF7. exact Hfhi.
  - rewrite ELP. discriminate.
  - rewrite ELP. vm_compute. reflexivity.
  - reflexivity.
  - exact I.
  - exact Hw0.
  - exact Hstr.
  - exact Hwaddr.
  - exact Hwamem.
  - lia.
  - unfold zdisjoint in Hsep |- *. cbn [fst snd] in Hsep |- *. rewrite Hpr. unfold RtPFShared.str_end.
    lazymatch goal with |- context [?e mod 8] => pose proof (Z.mod_pos_bound e 8 ltac:(lia)) end.
    lia.
  - unfold RtPFShared.str_end.
    lazymatch goal with |- context [?e mod 8] => pose proof (Z.mod_pos_bound e 8 ltac:(lia)) end.
    unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - lia.
  - exact Hfrm. }
intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & (H10 & HBY) & HKP).
rewrite Esl in HBY, HKP. rewrite Esb in HBY.
(* the callee-saved registers *)
assert (KR2 : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r z Hz Hr; exact (s20b_pres_reg _ _ r z HP2 Hz Hr)).
assert (RK2 : s20_rkept (ms_regs ms) regs2).
{ unfold s20_rkept.
  rewrite (KR2 2%bv 2), (KR2 3%bv 3), (KR2 4%bv 4), (KR2 8%bv 8), (KR2 9%bv 9)
    by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  repeat (split; [reflexivity|]). reflexivity. }
assert (KPT : s20_kept B cx c m W (ms_mem ms) W mem2).
{ eapply s20_kept_of_win with (lo := x_s1 cx - RtPFSeg.SEG_SNP_K); try eassumption.
  - unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - intros a Ha H1 H2. apply HKP; [exact Ha | |].
    + intros Hq. apply H1. unfold RtPFSeg.SEG_SNP_K, ESTACK in *. lia.
    + intros Hq. apply H2. lia. }
assert (Hctx2 : s20_ctx B MT cx ly S W regs2 mem2 md2 k acc LFO_P c m).
{ eapply s20_ctx_carry; try eassumption; first [exact RK2 | exact KPT | apply Permutation_refl]. }
unfold lt_post. eapply (srr_apost_baseF_lift _ fx1); [exact Hfx|].
apply (HAA fx1 cx ly S W regs2 mem2 md2 k acc c m HB (fxrel_frm0 fx fx1 Hfrm Hfx) Hlt Hctx2).
- unfold s20_lregs.
  rewrite (KR2 18%bv 18), (KR2 19%bv 19), (KR2 20%bv 20), (KR2 21%bv 21), (KR2 22%bv 22), (KR2 23%bv 23),
    (KR2 25%bv 25), (KR2 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite (KR 18%bv ltac:(cbn; tauto)), (KR 19%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)),
    (KR 21%bv ltac:(cbn; tauto)), (KR 22%bv ltac:(cbn; tauto)), (KR 23%bv ltac:(cbn; tauto)),
    (KR 25%bv ltac:(cbn; tauto)), (KR 26%bv ltac:(cbn; tauto)).
  split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
  split; [exact R22|]. split; [exact R23|]. split; [exact R25 | exact R26].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  pose proof (HBY (Z.of_nat j) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. exact Hb.
Qed.


(* ================= piece S20Find: s20_L2, s20_L4 (S11 / S12 piece c) ================= *)


(* the entry sp and the base register s1: S1 = (SP0 - 352) & ~31 *)
Lemma s20c_bounds : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 384 <= x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold STK_LLVMFuzzerTestOneInput in Hslo.
unfold x_s1, x_sp0, LT_FRAME. set (s := spZ (x_regs cx)) in *.
pose proof (Z.div_mod s 16 ltac:(lia)) as D1. pose proof (Z.div_mod (s - 352) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (s - 352) 32 ltac:(lia)) as M2.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (s - 352 - (s - 352) mod 32) with ((s - 352) / 32 * 32) by lia. apply Z.mod_mul. lia.
- lia.
Qed.

(* the class-3 frame of a point: in the state's frames at x_fr, 32-aligned, present, below the ceiling *)
Lemma s20c_frame : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a).
Proof.
intros cx ly S W regs mem md k o HF.
destruct HF as (HJ & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
assert (Efa : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (Hal & _ & Hpr & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (H4 & Hc & _).
rewrite Efa in Hal, Hpr, H4, Hc. change (fs_frame_bytes LT_FCLS) with 512 in Hpr, Hc.
split; [exact Hin|]. split; [exact Efa|]. split; [exact Hal|]. split; [exact H4|]. split; [exact Hc|].
intros a Ha. exact (proj1 (Hpr a Ha)).
Qed.

(* s20_ctx carried to a state that the journal reaches, that keeps every byte outside a window below s1 and
   whose registers the call preserved; the state allocates nothing (sa_noalloc) *)
Lemma s20c_carry : forall cx ly S (W : world SEGS) regs mem md k acc o c m
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 lo,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved regs regs2 ->
  alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  (exists f, S2 = set_fs f S) ->
  s20_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 k acc o c m.
Proof.
intros cx ly S W regs mem md k acc o c m ly2 S2 W2 regs2 mem2 md2 lo HB HCTX HJ2 HP Hlo HK HPerm [f HS2].
assert (HRK : s20_rkept regs regs2).
{ unfold s20_rkept.
  split; [exact (s20c_pres regs regs2 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20c_pres regs regs2 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20c_pres regs regs2 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20c_pres regs regs2 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  exact (s20c_pres regs regs2 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). }
assert (HKP : s20_kept B cx c m W mem W2 mem2).
{ eapply s20_kept_of_win with (lo := lo); try eassumption.
  intros a Ha Hw _. exact (HK a Ha Hw). }
assert (HBUD : lt_bud MT cx S2 k acc 6).
{ pose proof HCTX as HC2. destruct HC2 as ((_ & _ & _ & Hb) & _).
  destruct Hb as (Hk0 & Hr0 & Hkr & Hmo & Hacc & Hxm).
  split; [exact Hk0|]. split; [exact Hr0|]. split; [exact Hkr|].
  split; [rewrite HS2; (eapply mo_le_set_fs_r; eassumption)|]. split; [exact Hacc | exact Hxm]. }
eapply s20_ctx_carry; try eassumption.
Qed.

(* the same across a straight run: the run's journal at the same allocator state, every byte kept *)
Lemma s20c_run_carry : forall cx ly S (W : world SEGS) regs mem md k acc o c m regs2 mem2 md2,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  aregs_preserved regs regs2 -> (forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a) ->
  s20_ctx B MT cx ly S W regs2 mem2 md2 k acc o c m.
Proof.
intros cx ly S W regs mem md k acc o c m regs2 mem2 md2 HB HC HJ HP HK.
destruct (s20c_bounds cx HB) as (_ & Bac & _ & _ & Bs1).
eapply (s20c_carry cx ly S W regs mem md k acc o c m ly S W regs2 mem2 md2 (x_s1 cx));
  [exact HB | exact HC | exact HJ | exact HP | lia | intros a Ha _; exact (HK a Ha) | apply Permutation_refl
  | exists (st_fs S); destruct S; reflexivity].
Qed.

(* the three slot words of the seed and s1, at a point of either segment *)
Lemma s20c_slots : forall cx ly S (W : world SEGS) regs mem md k acc o c m,
  s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  rdword (rdW W mem) (x_s1 cx + 120) = Some (s20_probe cx) /\ rdword (rdW W mem) (x_s1 cx + 168) = Some c /\
  rdword (rdW W mem) (x_s1 cx + 192) = Some m /\ getr regs 9 = w64 (x_s1 cx).
Proof.
intros cx ly S W regs mem md k acc o c m (HCORE & _ & _ & HSL & _).
pose proof HCORE as ((_ & _ & _ & _ & _ & F9 & _) & _).
split; [apply HSL; apply in_or_app; right; left; reflexivity|].
split; [apply HSL; apply in_or_app; left; unfold LT_LC; cbn [In]; repeat (first [left; reflexivity | right])|].
split; [apply HSL; apply in_or_app; left; unfold LT_LC; cbn [In]; repeat (first [left; reflexivity | right])|].
exact F9.
Qed.

(* the seed at a point of the segment, from s20_ctx *)
Lemma s20c_seed_ctx : forall cx ly S (W : world SEGS) regs mem md k acc o c m pc alo ahi,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  alo <= bv_unsigned (getr regs 10) <= ahi ->
  st_ok_pi SEGS VAL (s20c_E regs (s20_probe cx) c m) (s20c_ss pc alo ahi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S20Cx [] (s20c_E regs (s20_probe cx) c m) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (s20c_E regs (s20_probe cx) c m).
Proof.
intros cx ly S W regs mem md k acc o c m pc alo ahi HB HC Ha0.
destruct (s20c_bounds cx HB) as (_ & Bac & B47 & _ & Bs1).
pose proof asan_consts as (C1 & _).
destruct (s20c_slots cx ly S W regs mem md k acc o c m HC) as (Hp & Hc & Hm & F9).
apply (s20c_seed pc alo ahi W regs mem (x_s1 cx) (s20_probe cx) c m F9); [lia | lia | exact Ha0 | exact Hp | exact Hc
  | exact Hm].
Qed.

(* any a0 lies in [0, 2 ^ 64 - 1] *)
Lemma s20c_a0_any : forall regs, 0 <= bv_unsigned (getr regs 10) <= 2 ^ 64 - 1.
Proof.
intros regs. pose proof (bv_unsigned_in_range 64 (getr regs 10)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

(* the events spent so far leave room for a callee that spends none *)
Lemma s20c_nev : forall cx ly S (W : world SEGS) regs mem md k acc o c m, lt_base B MT cx ->
  s20_ctx B MT cx ly S W regs mem md k acc o c m -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W regs mem md k acc o c m HB HC.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
destruct HC as (((HJ & _) & _ & _ & (Hk0 & Hr0 & Hkr & _)) & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
Qed.

(* the probe of a point, in scope and holding T and its NUL: where it lies, its tail, its shadow, its frame *)
Lemma s20c_probe : forall cx ly S (W : world SEGS) regs mem md k acc c m (T : list Z),
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m ->
  (length T <= 16)%nat ->
  4096 <= s20_probe cx /\ s20_probe cx + 18 <= alloc_ceiling /\
  sa_tail (rdW W mem) (s20_probe cx + Z.of_nat (length T)) /\
  sa_addr (rdW W mem) (s20_probe cx) (Z.of_nat (length T) + 1) /\
  sa_addr (rdW W mem) (s20_probe cx) (Z.of_nat (length T)) /\
  sa_fframe ly S (s20_probe cx) (Z.of_nat (length T) + 1) /\
  sa_fframe ly S (s20_probe cx) (Z.of_nat (length T)).
Proof.
intros cx ly S W regs mem md k acc c m T HB HC HL.
pose proof HC as ((HFR & _) & _).
destruct (s20c_frame cx ly S W regs mem md k LFO_P HFR) as (Hin & Efa & Hal & H4 & Hc & Hpr).
assert (HPA : sa_addr (rdW W mem) (s20_probe cx) 18)
  by (eapply s20_probe_addr; first [exact HFR | reflexivity | exact IMGF | eassumption]).
assert (FF : forall n, 0 <= n <= 18 -> sa_fframe ly S (s20_probe cx) n).
{ intros n Hn. exists LT_FCLS, (x_fpos cx). split; [exact Hin|]. split; [unfold LT_FCLS; lia|].
  rewrite Efa. change (fs_frame_bytes LT_FCLS) with 512. unfold s20_probe, FO_PROBE. lia. }
unfold s20_probe, FO_PROBE in *.
split; [lia|]. split; [lia|]. split.
- intros x Hx. eapply aview_some_of_apresent. apply Hpr.
  pose proof (Z.mod_pos_bound (x_fr cx + 192 + Z.of_nat (length T)) 8 ltac:(lia)). lia.
- split; [apply (s20c_addr_le _ _ 18); [exact HPA | lia]|].
  split; [apply (s20c_addr_le _ _ 18); [exact HPA | lia]|].
  split; apply FF; lia.
Qed.

(* the probe's bytes survive a call whose window lies in [lo, s1), lo above the allocator ceiling *)
Lemma s20c_probe_kept : forall cx (rd rd' : reader) lo l,
  lt_base B MT cx -> alloc_ceiling <= lo -> 0 <= s20_probe cx -> s20_probe cx + 18 <= alloc_ceiling ->
  (length l <= 18)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < x_s1 cx) -> rd' a = rd a) ->
  sa_zs rd (s20_probe cx) l -> sa_zs rd' (s20_probe cx) l.
Proof.
intros cx rd rd' lo l HB Hlo Hp0 Hp18 Hl HK.
pose proof asan_consts as (C1 & _).
apply s20c_zs_kept. intros x Hx. apply HK; lia.
Qed.

(* a program call from a point of the segment (sp = s1) to a callee with no footprint and no allocator event
   whose post P keeps every byte outside its window (m_find, check_absent), through PaCall's cl_callS; back at
   BASE + ret the walk's journal holds again and s20_ctx is carried *)
Lemma s20c_call : forall cx ly S (W : world SEGS) regs mem md k acc o c m (STKF AF ret : Z)
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) Q,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  0 <= STKF <= ASTACK -> getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall ly' S' (W' : world SEGS) regs' mem' md', P ly' S' W' regs' mem' md' ->
     sa_kept SEGS W mem W' mem' regs STKF (fun _ => False) /\ sa_noalloc B ly S ly' S') ->
  (forall ch, afn_pre SEGS B STKF ly S W regs mem md ch ->
     SRr SEGS W (cfg_at SEGS AF regs mem md) (apost_base SEGS B STKF [] regs ly S W mem md 0 P)) ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2, wle W W2 ->
     s20_ctx B MT cx ly S2 W2 regs2 mem2 md2 k acc o c m ->
     aregs_preserved regs regs2 -> P ly S2 W2 regs2 mem2 md2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - STKF <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 AF) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m STKF AF ret P Q HBASE HCTX HSTK R1 Hret Hret2 HPK HCALLEE HK.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof HBASE as (HPRE0 & HPRES0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HCTX as (HCORE & _).
destruct HCORE as (HFR & _ & _ & _).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0 : s0Z regs = x_sp0 cx).
{ unfold s0Z. rewrite F8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* the frame chain at the call: the stack from s1 up is readable (the entry's astack_pres, kept by the journal) *)
assert (HRD : astack_rd ly (rdW W mem) (x_s1 cx)).
{ apply (astack_rd_of_pres SEGS). apply (astack_pres_mono _ _ _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
  - unfold STK_LLVMFuzzerTestOneInput. lia.
  - eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HPRES0 |].
    intros a (r & Hr & Ha) Ha2. exfalso. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch & Hch).
eapply SRr_bind.
{ apply (cl_callS B LAWS W regs mem (Z_to_bv 64 AF) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STKF [] 0
    (x_s1 cx - x_sp0 cx) (getr regs 1) ch P HJ Hsp).
  - pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
    replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
    + apply Z.mod_mul. lia.
    + pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia.
  - lia.
  - lia.
  - unfold STK_LLVMFuzzerTestOneInput, ASTACK in *. lia.
  - rewrite F3. exact Hgp0.
  - rewrite F4. exact Htp0.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia. rewrite Hs0. exact Hch.
  - intros HPRE. exact (HCALLEE ch HPRE).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & HX).
destruct (HPK _ _ _ _ _ _ HX) as (Hkp & Hna).
rewrite Z.add_0_r in HJ2. rewrite R1.
pose proof Hna as (HPerm & -> & Hfs).
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - STKF <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha Hw. apply (Hkp a Ha); [|tauto]. unfold spZ. rewrite F2. unfold w64.
  rewrite unsigned_lit_small by lia. exact Hw. }
apply (HK S2 W2 regs2 mem2 md2 Hle); [| exact HP | exact HX | exact HKEEP].
eapply (s20c_carry cx ly S W regs mem md k acc o c m ly S2 W2 regs2 mem2 md2 (x_s1 cx - STKF));
  [exact HBASE | exact HCTX | exact HJ2 | exact HP | unfold ASTACK in HSTK; lia | exact HKEEP | exact HPerm
  | exact Hfs].
Qed.

(* the strlen wrapper at a point of the segment, through PaArt's aj_art_at (window ESTACK, Eb = False), in the
   donor's aw_snl_art_loc / aw_strnlen_loc form (fuzz_command _s41.v:377-454) *)
Lemma s20c_strlen : forall cx ly S (W : world SEGS) regs mem md k acc o c m (ret : Z) (x : Z) (s : list byte) Q,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regs 10 = w64 x -> 0 < x ->
  astr_at SEGS W mem x s ->
  aread_ok SEGS ESTACK W regs mem x (astr_len s + 1) ->
  atail_vis SEGS W mem (x + astr_len s) ->
  (forall regs2 mem2 md2,
     s20_ctx B MT cx ly S W regs2 mem2 md2 k acc o c m ->
     aregs_preserved regs regs2 -> getr regs2 10 = w64 (astr_len s) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W mem a) ->
     SRr SEGS W (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIG SS___interceptor_trampoline_strlen)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m ret x s Q HBASE HCTX R1 Hret Hret2 R10 Hx Hstr Hrd Htl HK.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof HBASE as (HPRE0 & HPRES0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HCTX as (HCORE & _).
destruct HCORE as (HFR & HIMG & _ & _).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Hsp : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
  replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
  - apply Z.mod_mul. lia.
  - pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia. }
assert (HraT : YK0s.ret_ok (getr regs 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | exact Hret2]).
(* the read-only image bytes the strlen interceptor reads, and the errno cell of the record *)
assert (HENV : api_env SEGS B)
  by (first [exact (pal_env B TL) | exact (pal_env TL) | exact (@pal_env _ _ _ B TL) | exact (@pal_env _ _ _ _ B TL)]).
assert (HROM : rt_rom_view SEGS B W mem).
{ destruct HIMG as (HRO & _ & _). intros a Hr Ho He. apply HRO; [left; exact Hr | exact Ho | exact He]. }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low HENV ESTACK (fun _ => False)
    (SIG SS___interceptor_trampoline_strlen) W regs mem STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k (x_s1 cx - x_sp0 cx)
    (getr regs 1) (fun regs' _ => getr regs' 10 = w64 (astr_len s))
    HJ Hsp Hal ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; lia) eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W regs mem md x s).
  - exact (ecall_pre_stk_at SEGS B ESTACK STK_LLVMFuzzerTestOneInput (x_sp0 cx)
      (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k
      regs (x_s1 cx - x_sp0 cx) HJ Hsp Hal ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; lia) HraT
      ltac:(rewrite F3; exact Hgp0) ltac:(rewrite F4; exact Htp0)).
  - exact R10.
  - exact Hx.
  - exact Hstr.
  - exact Hrd.
  - exact Htl.
  - exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & HK2).
rewrite R1.
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W mem a).
{ intros a Ha Hw. apply (HK2 a Ha); [|tauto]. replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  exact Hw. }
apply (HK regs2 mem2 md2); [| exact HP | exact HQ | exact HKEEP].
eapply (s20c_carry cx ly S W regs mem md k acc o c m ly S W regs2 mem2 md2 (x_s1 cx - ESTACK));
  [exact HBASE | exact HCTX | exact HJ2 | exact HP | rewrite Hes; lia | exact HKEEP | apply Permutation_refl
  | exists (st_fs S); destruct S; reflexivity].
Qed.

(* ---- the facts the two segments read at a point ---- *)
(* the two harness blocks of s20_ctx: m holds the model state, c the reader state *)
Lemma s20c_blks : forall cx ly S (W : world SEGS) regs mem md k acc o c m,
  s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  m <> 0 /\ m mod 16 = 0 /\ sa_mconf (rdW W mem) m (x_mcF cx) /\ sa_heap B ly S m seg_spec.SEG_M_SIZE /\
  sa_addr (rdW W mem) m seg_spec.SEG_M_SIZE /\ 4096 <= m /\ m + seg_spec.SEG_M_SIZE <= 2 ^ 63 /\
  c <> 0 /\ c mod 16 = 0 /\ sa_rconf (rdW W mem) c (x_rcF cx) /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
  sa_addr (rdW W mem) c seg_spec.SEG_C_SIZE /\ 4096 <= c /\ c + seg_spec.SEG_C_SIZE <= 2 ^ 63.
Proof.
intros cx ly S W regs mem md k acc o c m (_ & (HCin & Hc4 & Hc16 & HCad) & (HMin & Hm4 & Hm16 & HMad) & _ & HRC & HMC).
pose proof HCad as (_ & Hc63 & _). pose proof HMad as (_ & Hm63 & _).
split; [lia|]. split; [exact Hm16|]. split; [exact HMC|].
split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HMin | lia]|].
split; [exact HMad|]. split; [exact Hm4|]. split; [lia|].
split; [lia|]. split; [exact Hc16|]. split; [exact HRC|].
split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HCin | lia]|].
split; [exact HCad|]. split; [exact Hc4 | lia].
Qed.
(* m->n is at most 32 (KIT-1's s20_mconf_n) *)
Lemma s20c_mconf_n : forall rd m mc, sa_mconf rd m mc -> (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc H.
assert (H2 : sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\
  (length (SegModel.mc_seg mc) <= 32)%nat) by (eapply s20_mconf_n; eassumption).
exact (proj2 H2).
Qed.
(* turn i's probe text: no NUL, at most 16 bytes, and the harness's probe check of the run holds of it *)
Lemma s20c_T : forall cx i rd m, (i < length (SegModel.mc_seg (x_mcF cx)))%nat -> sa_mconf rd m (x_mcF cx) ->
  ~ In 0 (s20_T cx i) /\ (length (s20_T cx i) <= 16)%nat /\
  SegModel.probe_ok (x_rcF cx) (x_mcF cx) (s20_T cx i) = true.
Proof.
intros cx i rd m Hi Hmc.
assert (HN : sa_zs rd (seg_spec.mseg_addr m i)
    (SegModel.ms_name (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d) ++ [0]) /\
  ~ In 0 (SegModel.ms_name (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d)) /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d)) < 16)%nat /\
  (forall j, 0 <= j < 16 -> rd (seg_spec.mseg_addr m i + j) <> None)) by (eapply s20_mconf_name; eassumption).
destruct HN as (_ & Hnz & Hlen & _).
change (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d) with (x_seg cx i) in Hnz, Hlen.
split; [|split].
- unfold s20_T. rewrite in_app_iff. intros [H | [H | []]]; [exact (Hnz H) | discriminate H].
- unfold s20_T. rewrite length_app. cbn [length]. lia.
- destruct (s20_probe_ok_all (x_pl cx)) as (H1 & _).
  assert (Hin : In (x_seg cx i) (SegModel.mc_seg (x_mcF cx))) by (unfold x_seg; apply nth_In; exact Hi).
  pose proof (proj1 (forallb_forall _ _) H1 (x_seg cx i) Hin) as H.
  cbv beta in H. rewrite (s20_probe_text (SegModel.ms_name (x_seg cx i)) Hnz ltac:(lia)) in H. exact H.
Qed.
(* a byte list the reader holds is mapped *)
Lemma s20c_zs_some : forall (rd : reader) a l x, sa_zs rd a l -> a <= x < a + Z.of_nat (length l) -> rd x <> None.
Proof.
intros rd a l x H Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.
(* the probe loop's registers survive what preserves the callee-saved registers *)
Lemma s20c_lregs_pres : forall cx regs regs2 m i, aregs_preserved regs regs2 -> s20_lregs cx regs m i ->
  s20_lregs cx regs2 m i.
Proof.
intros cx regs regs2 m i HP (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
unfold s20_lregs.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
  match goal with |- getr regs2 ?r = _ => rewrite (s20c_pres_eq regs regs2 r HP ltac:(s20c_cs)) end; assumption.
Qed.
(* the literal "nosuch0" (A_OBJ 8 = 0x21040) and its facts from seg_himg *)
Lemma s20c_obj8 : VAL (A_OBJ 8) = seg_litA_fz LIT_NOSUCH.
Proof. rewrite (VOBJS 8%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma s20c_nosuch_lit : forall cx rd, lt_img B cx rd -> sa_lit SEGS B rd (VAL (A_OBJ 8)) LIT_NOSUCH.
Proof.
intros cx rd (_ & HH & _). destruct HH as (_ & _ & HLIT & _). rewrite s20c_obj8.
refine (proj1 (HLIT LIT_NOSUCH _)).
unfold LTOI_FZ_LITS. apply in_or_app. left. unfold LTOI_LITS. cbn [In].
repeat first [left; reflexivity | right].
Qed.
(* the image atom a1 holds after the auipc / addi of "nosuch0" (A_OBJ 8 = atom 249) *)
Ltac s20c_a1 E HEI :=
  first [ exact (s20c_E_img E (A_OBJ 8) HEI ltac:(vm_compute; lia))
        | reflexivity
        | lazymatch goal with |- ?G => fail 100 "s20c_a1:" G end ].
(* the condition of `bnez a0` after the branch split, with a0 = w64 v: negb (v =? 0) *)
Ltac s20c_bne Hc EEo R10 :=
  cbn [branch_taken sv_denot] in Hc; unfold bv_eqb in Hc;
  rewrite ?(EEo 10%nat 10%bv eq_refl) in Hc; rewrite ?R10 in Hc; unfold w64 in Hc;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc; rewrite ?unsigned_lit_small in Hc by lia.

(* ---- segment N -> NZ: m_find(m, "nosuch0", 7) and, on a miss, check_absent(c, "nosuch0") ---- *)
(* 0x8595c: m_find returned its answer on "nosuch0" *)
Lemma s20c_at_NMRA : S20_NZ_stmt B MT ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> s20_ctx B MT cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) LIT_NOSUCH) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_NMRA) regs mem md) (lt_post B MT cx).
Proof.
intros HNZ cx ly S W regs mem md k acc c m HBASE HFRM HCTX R10.
unfold S20_NZ_stmt in HNZ.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (s20c_blks cx ly S W regs mem md k acc LFO0 c m HCTX)
  as (Hm0 & Hm16 & Hmc & Hmh & Hma & Hm4 & Hm63 & _).
pose proof (s20c_mconf_n _ _ _ Hmc) as Hn32.
pose proof HCTX as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s20_m_find_ptr_cases m (x_mcF cx) LIT_NOSUCH Hm4 Hm63 Hn32) as [(Hmiss & Hptr) | (j & Hfind & Hptr & Hj)];
  rewrite Hptr in R10.
- (* miss: a1 = "nosuch0", a0 = c, check_absent, back at NZ *)
  destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO0 c m LO_NMRA 0 0 HBASE HCTX
    ltac:(rewrite R10; unfold w64; rewrite unsigned_lit_small by lia; lia)) as (HS & SHOK & HEI).
  pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
  assert (E33 : ew (s20c_E regs (s20_probe cx) c m) 33 = Z_to_bv 64 c)
    by exact (s20c_E_extra regs (s20_probe cx) c m 1 ltac:(lia)).
  remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* bnez a0 with a0 = 0: not taken *)
  psrr_branch_tok RUN BR HS SHOK S20Cspan.
  { exfalso. s20c_bne Hc EEo R10. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK S20Cspan.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
  pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
    as HC1.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite (SIGP SS_check_absent ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  replace (seg_af SS_check_absent) with AF_check_absent by (vm_compute; reflexivity).
  destruct (s20c_blks cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m HC1)
    as (_ & _ & _ & _ & _ & _ & _ & Hc0 & Hc16 & Hrc & Hch & Hca & Hc4 & Hc63).
  pose proof HC1 as ((HFR1 & HIMG1 & _) & _). pose proof HIMG1 as (HRO1 & _).
  pose proof (s20c_nosuch_lit cx _ HIMG1) as (Hl0 & Hlstr & Hlpin & _ & Hlimg).
  assert (HLN : Z.of_nat (length LIT_NOSUCH) = 7) by (vm_compute; reflexivity).
  assert (HV8 : VAL (A_OBJ 8) = 0x21040) by (rewrite s20c_obj8; vm_compute; reflexivity).
  rewrite HLN in Hlpin, Hlimg.
  pose proof (Hlpin _ _ _ _ _ (proj1 (proj1 HFR1))) as Hla.
  apply (s20c_call cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m STK_check_absent (BASE + AF_check_absent)
    LO_NZ (fun ly' S' W' regs' mem' md' =>
      sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_check_absent (fun _ => False) /\ sa_noalloc B ly S ly' S')
    (lt_post B MT cx) HBASE HC1).
  + pose proof STK_values as SV. unfold ASTACK. lia.
  + rewrite P1. reflexivity.
  + unfold LO_NZ. lia.
  + reflexivity.
  + intros ly' S' W' regs' mem' md' H. exact H.
  + intros ch HPRE.
    apply (HCHECK_ABSENT fx ly S W (ms_regs ms) (ms_mem ms) md1 ch c (VAL (A_OBJ 8)) (x_rcF cx) LIT_NOSUCH HPRE HRO1).
    * rewrite P10, E33. reflexivity.
    * unfold seg_spec.SEG_C_SIZE in Hc63. lia.
    * rewrite P11. s20c_a1 E HEI.
    * rewrite HV8. lia.
    * split.
      -- unfold query_pre. rewrite HLN.
         split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hrc|]. split; [exact Hch|]. split; [exact Hca|].
         split; [lia|]. split; [exact Hlstr|]. split; [right; right; exact Hlimg|]. split; [exact Hla | lia].
      -- exact (s20_absent_of (x_rcF cx) (x_mcF cx) LIT_NOSUCH (proj2 (s20_probe_ok_all (x_pl cx))) Hmiss).
    * unfold check_absent_c.EV_check_absent.
      pose proof (s20c_nev cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m HBASE HC1). lia.
  + intros S2 W2 regs2 mem2 md2 Hle HC2 HP2 _ _.
    exact (HNZ cx ly S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM HC2).
- (* found: bnez to NZ *)
  destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO0 c m LO_NMRA 0 (2 ^ 64 - 1) HBASE HCTX
    (s20c_a0_any regs)) as (HS & SHOK & HEI).
  pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
  remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* bnez a0 with a0 = m->seg[j] <> 0: taken *)
  psrr_branch_tok RUN BR HS SHOK S20Cspan.
  2: { exfalso. s20c_bne Hc EEo R10. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK S20Cspan LO_NZ.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
  pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
    as HC1.
  pmkst HS.
  exact (HNZ cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m HBASE HFRM HC1).
Qed.

(* 0x85948 .. 0x85958: a1 = "nosuch0", a2 = 7, a0 = 192(s1) = m, jal m_find *)
Lemma s20_L4 : S20A_NZ B MT -> S20_N_stmt B MT.
Proof.
intros HNZA. unfold S20_N_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM HCTX.
pose proof (HNZA fx) as HNZ. clear HNZA.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO0 c m LO_N 0 (2 ^ 64 - 1) HBASE HCTX (s20c_a0_any regs))
  as (HS & SHOK & HEI).
pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
assert (E34 : ew (s20c_E regs (s20_probe cx) c m) 34 = Z_to_bv 64 m)
  by exact (s20c_E_extra regs (s20_probe cx) c m 2 ltac:(lia)).
remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK S20Cspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
  as HC1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
rewrite (SIGP SS_m_find ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
replace (seg_af SS_m_find) with AF_m_find by (vm_compute; reflexivity).
destruct (s20c_blks cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m HC1)
  as (Hm0 & Hm16 & Hmc & Hmh & Hma & Hm4 & Hm63 & _).
pose proof HC1 as ((HFR1 & HIMG1 & _) & _). pose proof HIMG1 as (HRO1 & _).
pose proof (s20c_nosuch_lit cx _ HIMG1) as (Hl0 & Hlstr & Hlpin & _ & Hlimg).
assert (HLN : Z.of_nat (length LIT_NOSUCH) = 7) by (vm_compute; reflexivity).
assert (HZB : seg_spec.zs (seg_spec.zb LIT_NOSUCH) = LIT_NOSUCH) by (vm_compute; reflexivity).
assert (HV8 : VAL (A_OBJ 8) = 0x21040) by (rewrite s20c_obj8; vm_compute; reflexivity).
rewrite HLN in Hlpin, Hlimg.
pose proof (Hlpin _ _ _ _ _ (proj1 (proj1 HFR1))) as Hla.
destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms) (VAL (A_OBJ 8)) LIT_NOSUCH (proj1 Hlstr)) as (Hb & _ & _).
apply (s20c_call cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m STK_m_find (BASE + AF_m_find) LO_NMRA
  (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) (seg_spec.zs (seg_spec.zb LIT_NOSUCH))) /\
     sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_m_find (fun _ => False) /\ sa_noalloc B ly S ly' S')
  (lt_post B MT cx) HBASE HC1).
- pose proof STK_values as SV. unfold ASTACK. lia.
- rewrite P1. reflexivity.
- unfold LO_NMRA. lia.
- reflexivity.
- intros ly' S' W' regs' mem' md' (_ & Hk & Hn). exact (conj Hk Hn).
- intros ch HPRE.
  apply (HM_FIND fx ly S W (ms_regs ms) (ms_mem ms) md1 ch m (VAL (A_OBJ 8)) 7 (x_mcF cx) (seg_spec.zb LIT_NOSUCH)
    HPRE HRO1).
  + rewrite P10, E34. reflexivity.
  + unfold seg_spec.SEG_M_SIZE in Hm63. lia.
  + rewrite P11. s20c_a1 E HEI.
  + rewrite HV8. lia.
  + rewrite P12. reflexivity.
  + lia.
  + unfold m_find_c.m_find_pre.
    split; [exact Hm0|]. split; [exact Hm16|]. split; [exact Hmc|]. split; [exact Hmh|]. split; [exact Hma|].
    split; [exact (s20c_bytes_app_l _ _ _ _ Hb)|].
    split; [rewrite s20c_zb_len; exact HLN|].
    split; [apply (s20c_addr_le _ _ (7 + 1)); [exact Hla | lia]|].
    right; right. apply (s20c_img_le B _ (7 + 1)); [exact Hlimg | lia].
  + unfold m_find_c.EV_m_find.
    pose proof (s20c_nev cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO0 c m HBASE HC1). lia.
- intros S2 W2 regs2 mem2 md2 Hle HC2 HP2 (R10' & _ & _) HK2.
  rewrite HZB in R10'.
  exact (s20c_at_NMRA HNZ cx ly S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM HC2 R10').
Qed.

(* ---- segment A i -> Z i: strlen(probe), m_find(m, probe, len) and, on a miss, check_absent(c, probe) ---- *)
(* 0x858f8: m_find returned its answer on turn i's probe text *)
Lemma s20c_at_MFRA : forall i, S20_Z_stmt B MT i ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m -> s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  getr regs 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) (s20_T cx i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_MFRA) regs mem md) (lt_post B MT cx).
Proof.
intros i HZ cx ly S W regs mem md k acc c m HBASE HFRM Hi HCTX HLR HPZ R10.
unfold S20_Z_stmt in HZ.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (s20c_blks cx ly S W regs mem md k acc LFO_P c m HCTX)
  as (Hm0 & Hm16 & Hmc & Hmh & Hma & Hm4 & Hm63 & _).
pose proof (s20c_mconf_n _ _ _ Hmc) as Hn32.
destruct (s20c_T cx i _ m Hi Hmc) as (HTnz & HTlen & HPOK).
destruct (s20c_probe cx ly S W regs mem md k acc c m (s20_T cx i) HBASE HCTX HTlen) as (Hp4 & Hp18 & _).
pose proof HCTX as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s20_m_find_ptr_cases m (x_mcF cx) (s20_T cx i) Hm4 Hm63 Hn32) as [(Hmiss & Hptr) | (j & Hfind & Hptr & Hj)];
  rewrite Hptr in R10.
- (* miss: a0 = 168(s1) = c, a1 = 120(s1) = the probe, check_absent, back at Z i *)
  destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO_P c m LO_MFRA 0 0 HBASE HCTX
    ltac:(rewrite R10; unfold w64; rewrite unsigned_lit_small by lia; lia)) as (HS & SHOK & HEI).
  pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
  assert (E32 : ew (s20c_E regs (s20_probe cx) c m) 32 = Z_to_bv 64 (s20_probe cx))
    by exact (s20c_E_extra regs (s20_probe cx) c m 0 ltac:(lia)).
  assert (E33 : ew (s20c_E regs (s20_probe cx) c m) 33 = Z_to_bv 64 c)
    by exact (s20c_E_extra regs (s20_probe cx) c m 1 ltac:(lia)).
  remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* bnez a0 with a0 = 0: not taken *)
  psrr_branch_tok RUN BR HS SHOK S20Cspan.
  { exfalso. s20c_bne Hc EEo R10. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK S20Cspan.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
  pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO_P c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
    as HC1.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite (SIGP SS_check_absent ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  replace (seg_af SS_check_absent) with AF_check_absent by (vm_compute; reflexivity).
  destruct (s20c_probe cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m (s20_T cx i) HBASE HC1 HTlen)
    as (_ & _ & Htail & HA1 & _ & HF1 & _).
  assert (HPZ1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
  { apply (s20c_zs_kept (rdW W mem)); [|exact HPZ]. intros x Hx. apply KM.
    rewrite length_app in Hx. cbn [length] in Hx. lia. }
  destruct (s20c_blks cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m HC1)
    as (_ & _ & _ & _ & _ & _ & _ & Hc0 & Hc16 & Hrc & Hch & Hca & Hc4 & Hc63).
  pose proof HC1 as ((_ & (HRO1 & _) & _) & _).
  apply (s20c_call cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m STK_check_absent (BASE + AF_check_absent)
    LO_Z (fun ly' S' W' regs' mem' md' =>
      sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_check_absent (fun _ => False) /\ sa_noalloc B ly S ly' S')
    (lt_post B MT cx) HBASE HC1).
  + pose proof STK_values as SV. unfold ASTACK. lia.
  + rewrite P1. reflexivity.
  + unfold LO_Z. lia.
  + reflexivity.
  + intros ly' S' W' regs' mem' md' H. exact H.
  + intros ch HPRE.
    apply (HCHECK_ABSENT fx ly S W (ms_regs ms) (ms_mem ms) md1 ch c (s20_probe cx) (x_rcF cx) (s20_T cx i)
      HPRE HRO1).
    * rewrite P10, E33. reflexivity.
    * unfold seg_spec.SEG_C_SIZE in Hc63. lia.
    * rewrite P11, E32. reflexivity.
    * lia.
    * split.
      -- unfold query_pre.
         split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hrc|]. split; [exact Hch|]. split; [exact Hca|].
         split; [lia|]. split; [exact (conj (conj HPZ1 HTnz) Htail)|].
         split; [right; left; exact HF1|]. split; [exact HA1 | lia].
      -- exact (s20_absent_of (x_rcF cx) (x_mcF cx) (s20_T cx i) HPOK Hmiss).
    * unfold check_absent_c.EV_check_absent.
      pose proof (s20c_nev cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m HBASE HC1). lia.
  + intros S2 W2 regs2 mem2 md2 Hle HC2 HP2 _ HK2.
    apply (HZ cx ly S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi HC2).
    * exact (s20c_lregs_pres cx regs regs2 m i (s20c_pres_trans _ _ _ HP1 HP2) HLR).
    * exact (s20c_probe_kept cx (rdW W (ms_mem ms)) (rdW W2 mem2) (x_s1 cx - STK_check_absent) (s20_T cx i ++ [0])
        HBASE ltac:(pose proof STK_values as SV; lia) ltac:(lia) Hp18
        ltac:(rewrite length_app; cbn [length]; lia) HK2 HPZ1).
- (* found: bnez to Z i *)
  destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO_P c m LO_MFRA 0 (2 ^ 64 - 1) HBASE HCTX
    (s20c_a0_any regs)) as (HS & SHOK & HEI).
  pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
  remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  (* bnez a0 with a0 = m->seg[j] <> 0: taken *)
  psrr_branch_tok RUN BR HS SHOK S20Cspan.
  2: { exfalso. s20c_bne Hc EEo R10. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK S20Cspan LO_Z.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
  pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO_P c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
    as HC1.
  pmkst HS.
  apply (HZ cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m HBASE HFRM Hi HC1).
  + exact (s20c_lregs_pres cx regs (ms_regs ms) m i HP1 HLR).
  + apply (s20c_zs_kept (rdW W mem)); [|exact HPZ]. intros x Hx. apply KM.
    rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* 0x858e8: strlen returned the length of turn i's probe text *)
Lemma s20c_at_SLRA : forall i, S20_Z_stmt B MT i ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m -> s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  getr regs 10 = w64 (Z.of_nat (length (s20_T cx i))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_SLRA) regs mem md) (lt_post B MT cx).
Proof.
intros i HZ cx ly S W regs mem md k acc c m HBASE HFRM Hi HCTX HLR HPZ R10.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (s20c_blks cx ly S W regs mem md k acc LFO_P c m HCTX)
  as (_ & _ & Hmc & _ & _ & Hm4 & Hm63 & _).
destruct (s20c_T cx i _ m Hi Hmc) as (HTnz & HTlen & _).
destruct (s20c_probe cx ly S W regs mem md k acc c m (s20_T cx i) HBASE HCTX HTlen) as (Hp4 & Hp18 & _).
pose proof HCTX as ((HFR & _) & _). pose proof HFR as (HJ & _).
pose proof HLR as (_ & _ & _ & _ & _ & _ & R25 & R26).
destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO_P c m LO_SLRA 0 (2 ^ 64 - 1) HBASE HCTX (s20c_a0_any regs))
  as (HS & SHOK & HEI).
pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x858e8 .. 0x858f4: a2 = a0, a0 = s9 = m, a1 = s10 = the probe, jal m_find *)
paj_run_tok RUN HS HJ SHOK S20Cspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO_P c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
  as HC1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
rewrite (SIGP SS_m_find ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
replace (seg_af SS_m_find) with AF_m_find by (vm_compute; reflexivity).
destruct (s20c_probe cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m (s20_T cx i) HBASE HC1 HTlen)
  as (_ & _ & Htail & HA1 & HA0 & HF1 & HF0).
assert (HPZ1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
{ apply (s20c_zs_kept (rdW W mem)); [|exact HPZ]. intros x Hx. apply KM.
  rewrite length_app in Hx. cbn [length] in Hx. lia. }
destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms) (s20_probe cx) (s20_T cx i) (conj HPZ1 HTnz)) as (Hb & _ & Hzs).
destruct (s20c_blks cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m HC1)
  as (Hm0' & Hm16' & Hmc' & Hmh' & Hma' & _).
pose proof HC1 as ((_ & (HRO1 & _) & _) & _).
apply (s20c_call cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m STK_m_find (BASE + AF_m_find) LO_MFRA
  (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) (seg_spec.zs (seg_spec.zb (s20_T cx i)))) /\
     sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_m_find (fun _ => False) /\ sa_noalloc B ly S ly' S')
  (lt_post B MT cx) HBASE HC1).
- pose proof STK_values as SV. unfold ASTACK. lia.
- rewrite P1. reflexivity.
- unfold LO_MFRA. lia.
- reflexivity.
- intros ly' S' W' regs' mem' md' (_ & Hk & Hn). exact (conj Hk Hn).
- intros ch HPRE.
  apply (HM_FIND fx ly S W (ms_regs ms) (ms_mem ms) md1 ch m (s20_probe cx) (Z.of_nat (length (s20_T cx i)))
    (x_mcF cx) (seg_spec.zb (s20_T cx i)) HPRE HRO1).
  + rewrite P10, (EEo 25%nat 25%bv eq_refl). exact R25.
  + unfold seg_spec.SEG_M_SIZE in Hm63. lia.
  + rewrite P11, (EEo 26%nat 26%bv eq_refl). exact R26.
  + lia.
  + rewrite P12, (EEo 10%nat 10%bv eq_refl). exact R10.
  + lia.
  + unfold m_find_c.m_find_pre.
    split; [exact Hm0'|]. split; [exact Hm16'|]. split; [exact Hmc'|]. split; [exact Hmh'|]. split; [exact Hma'|].
    split; [exact (s20c_bytes_app_l _ _ _ _ Hb)|].
    split; [exact (s20c_zb_len (s20_T cx i))|].
    split; [exact HA0|].
    right; left; exact HF0.
  + unfold m_find_c.EV_m_find.
    pose proof (s20c_nev cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m HBASE HC1). lia.
- intros S2 W2 regs2 mem2 md2 Hle HC2 HP2 (R10' & _ & _) HK2.
  rewrite Hzs in R10'.
  apply (s20c_at_MFRA i HZ cx ly S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi HC2).
  + exact (s20c_lregs_pres cx regs regs2 m i (s20c_pres_trans _ _ _ HP1 HP2) HLR).
  + exact (s20c_probe_kept cx (rdW W (ms_mem ms)) (rdW W2 mem2) (x_s1 cx - STK_m_find) (s20_T cx i ++ [0]) HBASE
      ltac:(pose proof STK_values as SV; lia) ltac:(lia) Hp18 ltac:(rewrite length_app; cbn [length]; lia) HK2 HPZ1).
  + exact R10'.
Qed.

(* 0x858e0 .. 0x858e4: a0 = s10 = the probe, jal strlen *)
Lemma s20_L2 : forall i, S20A_Z B MT i -> S20_A_stmt B MT i.
Proof.
intros i HZA. unfold S20_A_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HCTX HLR HPZ.
pose proof (HZA fx) as HZ. clear HZA.
destruct (s20c_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (s20c_blks cx ly S W regs mem md k acc LFO_P c m HCTX) as (_ & _ & Hmc & _).
destruct (s20c_T cx i _ m Hi Hmc) as (HTnz & HTlen & _).
destruct (s20c_probe cx ly S W regs mem md k acc c m (s20_T cx i) HBASE HCTX HTlen) as (Hp4 & Hp18 & _).
pose proof HCTX as ((HFR & _) & _). pose proof HFR as (HJ & _).
pose proof HLR as (_ & _ & _ & _ & _ & _ & R25 & R26).
destruct (s20c_seed_ctx cx ly S W regs mem md k acc LFO_P c m LO_A 0 (2 ^ 64 - 1) HBASE HCTX (s20c_a0_any regs))
  as (HS & SHOK & HEI).
pose proof (fun n (r : bv 5) H => s20c_E_reg regs (s20_probe cx) c m n r H) as EEo.
remember (s20c_E regs (s20_probe cx) c m) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK S20Cspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20c_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HP1 : aregs_preserved regs (ms_regs ms)) by (s20c_preserved HS EEo).
pose proof (s20c_run_carry cx ly S W regs mem md k acc LFO_P c m (ms_regs ms) (ms_mem ms) md1 HBASE HCTX HJ HP1 KM)
  as HC1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
destruct (s20c_probe cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m (s20_T cx i) HBASE HC1 HTlen)
  as (_ & _ & Htail & HA1 & _ & _ & _).
assert (HPZ1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
{ apply (s20c_zs_kept (rdW W mem)); [|exact HPZ]. intros x Hx. apply KM.
  rewrite length_app in Hx. cbn [length] in Hx. lia. }
destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms) (s20_probe cx) (s20_T cx i) (conj HPZ1 HTnz)) as (Hb & Hbnz & _).
pose proof HC1 as ((HFR1 & _) & _). pose proof HFR1 as (_ & F2 & _).
apply (s20c_strlen cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m LO_SLRA (s20_probe cx)
  (seg_spec.zb (s20_T cx i)) (lt_post B MT cx) HBASE HC1).
- rewrite P1. reflexivity.
- unfold LO_SLRA. lia.
- reflexivity.
- rewrite P10, (EEo 26%nat 26%bv eq_refl). exact R26.
- lia.
- exact (conj Hb Hbnz).
- unfold astr_len. rewrite s20c_zb_len. apply s20c_aread; [exact HA1 | lia |].
  intros a Ha. split.
  + apply (s20c_zs_some _ _ _ _ HPZ1). rewrite length_app. cbn [length]. lia.
  + unfold ascratch_stk, spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
- unfold astr_len. rewrite s20c_zb_len. exact Htail.
- intros regs2 mem2 md2 HC2 HP2 R10' HK2.
  unfold astr_len in R10'. rewrite s20c_zb_len in R10'.
  apply (s20c_at_SLRA i HZ cx ly S W regs2 mem2 md2 k acc c m HBASE HFRM Hi HC2).
  + exact (s20c_lregs_pres cx regs regs2 m i (s20c_pres_trans _ _ _ HP1 HP2) HLR).
  + exact (s20c_probe_kept cx (rdW W (ms_mem ms)) (rdW W mem2) (x_s1 cx - ESTACK) (s20_T cx i ++ [0]) HBASE
      ltac:(unfold ESTACK; lia) ltac:(lia) Hp18 ltac:(rewrite length_app; cbn [length]; lia) HK2 HPZ1).
  + exact R10'.
Qed.


(* ================= piece S20Calloc: the calloc walk kit, s20_L5, s20_S12 (S11 / S12 piece d) ================= *)


(* ---------------- the S01 / S02 walk's call step (image B's s12k.v), adapted ---------------- *)
(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma s20d_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma s20d_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* the image facts of a point carried to a later reader at an AR state that agrees on every image byte the runtime
   does not own (all of seg_himg's objects are such bytes, sa_img; RELRO by cif_relro_img) and on the ROM bytes; the
   stack-protector cells from AR at the later state (SegRecCells.seg_rec_cells) *)
Lemma s20d_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  lt_img B cx (rdW W mem) ->
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' ly' S' md' (HRO & HIMG & HGI) HAR' HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s20d_lit_kept B W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & _ & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr];
    [exists s; split; [exact Hs | exact Hr] | exact (@cif_relro_img SK SEGS B IMGF a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s20d_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s20d_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HSY IMGF ly' S' W' mem' md' HAR')))|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.

(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped (the entry's astack_pres
   carried by the journal; longl, the footprint, is below the stack), and s0 = SP0 is at least S1 + 352 *)
Lemma s20d_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.

(* the facts of a point after one allocator call of the harness at sp = S1: the journal from the entry goes on with
   one event, the kept registers and every byte the facts read are the same, the new block joins the harness's
   (newest first), the budget pays one event; and (beyond the S01 / S02 walk's text) every old block of another
   size keeps its bytes *)
Lemma s20d_after_alloc : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res nb slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, nb)] ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => res <= a < res + req_size nb) ->
  mo_le MT S S2 (mo_malloc MT nb) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) /\
  lt_hblk B ly2 S2 (rdW W2 mem2) res nb /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) /\
  (forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> nb ->
     forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a).
Proof.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb slo HB HC Hrem Hnb HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HKc as (K1 & K2 & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HinF2 : In (LT_FCLS, x_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF).
assert (HinB2 : In (res, nb) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : frame_addr ly2 LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res nb LT_FCLS (x_fpos cx) HAR2 HinB2 HinF2) as Hsep.
rewrite EF2, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
(* an old block of another size: apart from the new one (AR's block law at the return) *)
assert (KB : forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> nb ->
  forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a).
{ intros b nb' Hin Hne a Ha.
  assert (Hin2 : In (b, nb') (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hin).
  assert (Hneq : (b, nb') <> (res, nb)) by (intros Heq; injection Heq as _ Heq; exact (Hne Heq)).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b nb' res nb HAR2 Hin2 HinB2 Hneq) as Hd.
  destruct (al_blocks _ _ LAWS ly S W memT md b nb' HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb').
  pose proof (req_size_pos nb' ltac:(lia)) as [_ Hq']. pose proof (req_size_pos nb ltac:(lia)) as [_ Hq].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  replace a with (b + (a - b)) by ring.
  apply (K2 b nb' (a - b) Hin ltac:(lia)). cbv beta. lia. }
split; [|split; [exact (s20d_hblk ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) | split; [exact KS | exact KB]]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s20d_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20d_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20d_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20d_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20d_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s20d_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s20d_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s20d_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s20d_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (s20d_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s20d_word_kept (rdW W memT)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (s20d_word_kept (rdW W memT)); [|exact H184]; intros x Hx; apply KS; lia.
- (* the image facts *)
  exact (s20d_img_kept cx W W2 memT mem2 ly2 S2 md2 HI HAR2 K3).
- (* the blocks *)
  unfold lt_blocks in *. rewrite Hbl.
  eapply Permutation_trans; [apply Permutation_app_tail; exact HBL|].
  cbn [app]. apply Permutation_sym. apply Permutation_cons_append.
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
  pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   184(s1), keeps sp, gp, tp, s0, s1 and the allocator state (its journal from the entry at the same count) *)
Lemma s20d_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s20d_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (s20d_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20d_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20d_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20d_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (s20d_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (s20d_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (s20d_img_kept cx W W mem mem' ly S md' HI (proj1 HJ')).
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* the premises an allocator call of the harness asks, from lt_core at the call *)
Lemma s20d_call_pre : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> s20d_bsum O + nb <= LIVE_LTOI ->
  spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  - LTOI_FRAME_MAX <= x_s1 cx - x_sp0 cx /\
  getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ st_nev S < EV_MAX /\
  blocks_bytes S + nb <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT nb).
Proof.
intros cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum.
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
split; [unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold EV_LTOI in *; lia|].
split.
{ rewrite (s20d_blocks_bytes B ly S), (s20d_bsum_perm _ _ HBL), s20d_bsum_app.
  unfold x_bl0. rewrite <- (s20d_blocks_bytes B (x_ly cx) (x_S cx)). unfold LIVE_LTOI in *. lia. }
apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT nb) MTL Hmo B4 M0). lia.
Qed.

(* ---- one call of the calloc wrapper (row 13, at the calloc trampoline) from a point where lt_core holds; the
   product m * n within YGCalloc.PRIM_MAX (64512), the row's primary-size premise; the continuation also gets the
   old blocks of another size kept ---- *)
Lemma s20d_calloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O (m n : Z) raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= m -> 0 <= n -> m * n <= 64512 -> s20d_bsum O + m * n <= LIVE_LTOI ->
  getr regsT 10 = w64 m -> getr regsT 11 = w64 n -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (m * n)) (rem - 1) o ((res, m * n) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res (m * n) ->
     zero_atA (rdW W2 mem2) res (m * n) ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     (forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> m * n ->
        forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_calloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O m n raw Q HB HC Hrem Hm Hn Hmn Hsum H10 H11 H1 Hraw Hra4 HK.
assert (Hmn0 : 0 <= m * n) by nia.
destruct (s20d_call_pre cx ly S W regsT memT md k acc rem o O (m * n) HB HC Hrem ltac:(lia) Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
destruct HCSTK as [Hc0 Hc1].
destruct (s20d_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
eapply SRr_bind.
{ exact (s20d_acalloc04_sub SEGS B LAWS pa_segs_low MT (SIG SS___interceptor_trampoline_calloc) cstk (ACALLOC4 fx)
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k m n (x_s1 cx - x_sp0 cx) raw ch HJ H10 H11 Hm Hn
    ltac:(unfold MALLOC_MAX; lia) ltac:(unfold YGCalloc.PRIM_MAX; lia) Hlv Hsp Ho16 Ho0 Hc0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & Hz & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (s20d_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res (m * n) _
  HB HC Hrem ltac:(lia) HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2 & HKB).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 Hz HPr Hres HK2 HKB).
Qed.

(* ---------------- s20_L5: 0x85970 .. 0x85980, then calloc(cap + 1, 18) to K85984 ---------------- *)
Lemma s20_L5 : LTA_K85984 B MT -> S20_NZ_stmt B MT.
Proof.
intros HKA. unfold S20_NZ_stmt.
intros cx ly S W regs mem md k acc c m HB Hfrm HCTX.
pose proof (HKA fx) as HK. clear HKA.
destruct HCTX as (HC & HHc & HHm & HSL & HCM).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s20d_cap_range (x_pl cx)) as Hcap. change (seg_spec.seg_cap (x_pl cx)) with (x_cap cx) in Hcap.
pose proof HC as (HF & _). pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
assert (Hw56 : rdword (rdW W mem) (x_s1 cx + 56) = Some (x_cap cx)).
{ apply HSL. apply in_or_app. left. unfold LT_LC. cbn [In]. right; right; right; right; right; left. reflexivity. }
pose proof (s20d_seed5 W regs mem (x_s1 cx) (x_cap cx) R9 ltac:(lia) ltac:(lia) ltac:(lia) Hw56) as HS.
assert (SHOK : sh_ok SEGS s20d_X [] (s20d_E regs [Z_to_bv 64 (x_cap cx)]) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20d_E regs [Z_to_bv 64 (x_cap cx)])) by (unfold s20d_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs [Z_to_bv 64 (x_cap cx)]) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ n rr Hn)).
assert (E32 : ew (s20d_E regs [Z_to_bv 64 (x_cap cx)]) 32 = Z_to_bv 64 (x_cap cx))
  by (unfold s20d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (s20d_E regs [Z_to_bv 64 (x_cap cx)]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x85970 .. 0x85980: s3 := 56(s1) = cap, s3 := cap + 1, a1 := 18, a0 := s3, jal calloc *)
paj_run_tok RUN HS HJ SHOK s20d_span.
{ change (ss_mem s20d_ss5) with s20d_rg5. unfold s20d_rg5.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (19%bv : bv 5) P19.
unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s20d_nowin_kept E _ W mem (ms_mem ms) HFr eq_refl) as KM.
pose proof (s20d_core_run cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
assert (Ucap : Z_to_bv 64 (bv_unsigned (ew E 32) + 1) = w64 (x_cap cx + 1)).
{ rewrite E32. unfold w64. rewrite YP03.unsigned_lit_small by lia. reflexivity. }
pose proof HHc as (HinC & _ & _ & Hc0 & Hc63 & _). pose proof HHm as (HinM & _ & _ & Hm0 & Hm63 & _).
assert (Htn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
eapply (s20d_calloc_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc 6 LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_cap cx + 1) 18 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [s20d_bsum snd]. unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, LIVE_LTOI. lia.
- rewrite P10. exact Ucap.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 tab HC2 HHt HZ HPr Hres HKS HKB.
  replace ((x_cap cx + 1) * 18) with (x_tabn cx) in HC2, HHt, HZ, HKB by (rewrite Htn; ring).
  replace (6 - 1) with 5 in HC2 by reflexivity.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s20d_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (x_tabn cx)) c m tab HB Hfrm HC2).
  + apply (s20d_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; right; left. reflexivity.
  + apply (s20d_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; left. reflexivity.
  + exact HHt.
  + exact HZ.
  + exact Hres.
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P19. exact Ucap.
  + apply (s20d_slots_kept cx (rdW W mem)); [intros o v Hin; exact (s20d_slots_rng _ _ _ o v Hin) | |].
    * intros a Ha. rewrite HKS by lia. apply KM. lia.
    * exact (s20d_slots_sub cx _ c m _ _ HSL).
  + apply (s20d_cm_kept (rdW W mem)); [| | exact HCM].
    * intros a Ha. rewrite (HKB c seg_spec.SEG_C_SIZE HinC ltac:(rewrite Htn; unfold seg_spec.SEG_C_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_C_SIZE in *. lia.
    * intros a Ha. rewrite (HKB m seg_spec.SEG_M_SIZE HinM ltac:(rewrite Htn; unfold seg_spec.SEG_M_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* ---------------- s20_S12: 0x85984 .. 0x85990, then calloc(cap + 1, 20) to K85994 ---------------- *)
Lemma s20_S12 : LTA_K85994 B MT -> LT_K85984_stmt B MT.
Proof.
intros HKA. unfold LT_K85984_stmt.
intros cx ly S W regs mem md k acc c m tab HB Hfrm HC HHc HHm HHt HZt R10 R19 HSL HCM.
pose proof (HKA fx) as HK. clear HKA.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s20d_seed0 LO_K85984 W regs mem) as HS.
assert (SHOK : sh_ok SEGS s20d_X [] (s20d_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20d_E regs [])) by (unfold s20d_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s20d_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs [] n rr Hn)).
pose proof HC as (HF & _). pose proof (proj1 HF) as HJ.
remember (s20d_E regs []) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x85984 .. 0x85990: s2 := a0 (tab), a1 := 20, a0 := s3 (cap + 1), jal calloc *)
paj_run_tok RUN HS HJ SHOK s20d_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s20d_nowin_kept E _ W mem (ms_mem ms) HFr eq_refl) as KM.
pose proof (s20d_cap_range (x_pl cx)) as Hcap. change (seg_spec.seg_cap (x_pl cx)) with (x_cap cx) in Hcap.
pose proof (s20d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof asan_consts as (C1 & _).
pose proof (s20d_core_run cx ly S W regs mem md k acc 5 LFO0
  [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof HHc as (HinC & _ & _ & Hc0 & Hc63 & _). pose proof HHm as (HinM & _ & _ & Hm0 & Hm63 & _).
pose proof HHt as (HinT & _ & _ & Ht0 & Ht63 & _).
assert (Htn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Hmn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
eapply (s20d_calloc_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc 5 LFO0
  [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_cap cx + 1) 20 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [s20d_bsum snd]. rewrite Htn. unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, LIVE_LTOI. lia.
- rewrite P10, (EEo 19%nat 19%bv eq_refl). exact R19.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 mt HC2 HHmt HZmt HPr Hres HKS HKB.
  replace ((x_cap cx + 1) * 20) with (x_mtn cx) in HC2, HHmt, HZmt, HKB by (rewrite Hmn; ring).
  replace (5 - 1) with 4 in HC2 by reflexivity.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s20d_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (x_mtn cx)) c m tab mt HB Hfrm HC2).
  + apply (s20d_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app].
    right; right; right; left. reflexivity.
  + apply (s20d_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; right; left. reflexivity.
  + apply (s20d_hblk ly2 S2 W2 mem2 md2 tab _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; left. reflexivity.
  + exact HHmt.
  + intros i Hi. rewrite (HKB tab (x_tabn cx) HinT ltac:(rewrite Htn, Hmn; lia) (tab + i) ltac:(lia)).
    rewrite KM by lia. exact (HZt i Hi).
  + exact HZmt.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P18, (EEo 10%nat 10%bv eq_refl). exact R10.
  + apply (s20d_slots_kept cx (rdW W mem)); [intros o v Hin; exact (s20d_slots_rng _ _ _ o v Hin) | | exact HSL].
    intros a Ha. rewrite HKS by lia. apply KM. lia.
  + apply (s20d_cm_kept (rdW W mem)); [| | exact HCM].
    * intros a Ha. rewrite (HKB c seg_spec.SEG_C_SIZE HinC ltac:(rewrite Hmn; unfold seg_spec.SEG_C_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_C_SIZE in *. lia.
    * intros a Ha. rewrite (HKB m seg_spec.SEG_M_SIZE HinM ltac:(rewrite Hmn; unfold seg_spec.SEG_M_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

End e.
End f.
End d.

(* ---- the two segment statements, at every FP state ---- *)
Section top. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGF : seg_img_facts SEGS B.
Hypothesis HSY : YF0m.SegBSyms B.

(* a premise of a lemma of the section above, at an FP state fx1: a hypothesis of this section (the image numbers
   by unification), a continuation in the context, or a contract given at every FP state *)
Ltac s20_close := solve [ eassumption | match goal with H : forall fx0 : YK11.FPState, _ |- _ => exact (H _) end ].

(* no turn i >= 32 of the probe loop is reached: H i asks i < m->n, and m->n <= 32 (mconf_encp) *)
Lemma s20_H_vacuous : forall i, (32 <= i)%nat -> S20A_H B MT i.
Proof.
intros i Hi fx1. unfold S20_H_stmt. intros * _ _ Hlt Hctx _. exfalso.
destruct Hctx as (_ & _ & _ & _ & [_ Hm]).
unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _).
unfold x_mcF in Hlt. lia.
Qed.

(* the probe loop, by downward induction on the turn: H i -> A i -> Z i -> (H (i + 1) | N) *)
Lemma s20_loop : S20A_N B MT -> forall i, S20A_H B MT i.
Proof.
intros HN.
assert (H : forall d i, (32 <= i + d)%nat -> S20A_H B MT i).
{ induction d as [|d IH]; intros i Hid.
  - apply s20_H_vacuous. lia.
  - pose proof (IH (Datatypes.S i) ltac:(lia)) as HS.
    assert (HZ : S20A_Z B MT i) by (intros fx1; eapply (@s20_L3 fx1 rc SK PI B MT); s20_close).
    assert (HA : S20A_A B MT i) by (intros fx1; eapply (@s20_L2 fx1 rc SK PI B MT); s20_close).
    intros fx1. eapply (@s20_L1 fx1 rc SK PI B MT); s20_close. }
intros i. exact (H 32%nat i ltac:(lia)).
Qed.

Theorem lt_seg_S12 : forall fx1 : YK11.FPState, lt_seg_S12_stmt (fx := fx1) B MT.
Proof. intros fx1 HK. eapply (@s20_S12 fx1 rc SK PI B MT); s20_close. Qed.

Theorem lt_seg_S11 : forall fx1 : YK11.FPState, lt_seg_S11_stmt (fx := fx1) B MT.
Proof.
intros fx1 HK.
assert (HNZ : S20A_NZ B MT) by (intros fx2; eapply (@s20_L5 fx2 rc SK PI B MT); s20_close).
assert (HN : S20A_N B MT) by (intros fx2; eapply (@s20_L4 fx2 rc SK PI B MT); s20_close).
pose proof (s20_loop HN 0%nat) as H0.
eapply (@s20_L0 fx1 rc SK PI B MT); s20_close.
Qed.
End top.
