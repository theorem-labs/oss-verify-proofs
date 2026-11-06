(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the
   shared part of the walk of LLVMFuzzerTestOneInput (0x80c40) from G 0x81afc (ent_build's case 0 after the digits,
   the reverse and the odd_ch part: pod.h:250) to J 0x82618 (the pod built, the call of pod_write_ent next), the
   statement lib/AU/HPgSeg.v hsu_piece_W7b_stmt at headamp_himg_B / headamp_bld_B. Proves no function (kind: segment
   lemma).

   THE SPLIT. The walk is cut at every call and at the two places the engine cannot address a computed pointer:
     A1  0x81afc -> 0x81b30   the param table entry's address, its UBSan bound test and its shadow check (pod.h:250)
     A2  0x81b30 -> 0x41c18   sep by bit 7 of p, parts[0..3] stored at R+0x178 .., the store check of parts[1]
                              (R+0x180), s5 := t1, n := 0, s2 := &parts[0], strlen(parts[0])
     B   0x81b98 -> 0x51d8c   one turn's 95 clamp and memcpy(t + n, parts[i], l)          (i = 0 .. 3)
     C   0x81bbc -> 0x41c18   n += l, the next part, strlen(parts[i+1])                   (i = 0 .. 2)
     D   0x81bbc -> 0x51d8c   n += l, the 95 clamp of ent_text, memcpy(e62.body, t, n)      (i = 3)
     E1  0x81bec -> 0x81c08   s2 := &pp->len, s4 := &e62, the UBSan bound test of e62.body + n, the NUL's address
     E2  0x81c08 -> 0x82618   NUL, e62.type = 8, e62.size = n + 1, t and ch out of scope, the reloads, j J
   Every block is a lemma from the block's first pc to a fixed pc in the shape cb_post: the journal kept (no event),
   the world kept, the I/O state kept (same_io from the block's model), every register outside clob kept, every byte
   outside the block's write set Wr kept, every present byte present, and R.

   REGISTERS AND REAL-FRAME CELLS the walk reads or writes (image B): s0 = S (x8), s1 = R (x9), s3 = (F >> 3) + K
   (x19), s11 = K (x27), s9 = &t = F + 0x20 (x25), s10 = p at G, then n (x26), s2 = &ch at G, then &parts[i] (x18),
   s7 = parts[i], e62.body (x23), s4 = l, then &e62 (x20), s5 := t1 = what is left of the input (x21), t1 (x6),
   a0 .. a3 (x10 .. x13), ra (x1); R+0x110 the cursor, R+0x118 = e62 + 8, R+0x130 = e62 = F + 0x210,
   R+0x138 = &pp->len, R+0x148 = pp, R+0xe8 = ~(e62 + 8), parts[0 .. 3] at R+0x178 .. R+0x198 (written). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code: the 91 words 0x81afc .. 0x81c64 ---- *)
Definition HW7B_G : Z := 0x81afc.
Definition hw7b_tbl : ctable := build_table rsegs HW7B_G 91 TEmpty.
Lemma hw7b_tbl_ok : table_ok rsegs hw7b_tbl.
Proof. apply build_table_ok0. unfold HW7B_G. lia. Qed.
(* the pcs the blocks start and end at *)
Definition HW7B_A2 : Z := 0x81b30.
Definition HW7B_STRLEN : Z := 0x41c18.         (* the strlen wrapper's trampoline, StrlenDef.STRLEN_ENTRY_B *)
Definition HW7B_MEMCPY : Z := 0x51d8c.         (* the runtime's memcpy entry *)
Definition HW7B_AFTER_STRLEN : Z := 0x81b98.
Definition HW7B_AFTER_MEMCPY : Z := 0x81bbc.
Definition HW7B_AFTER_TEXT : Z := 0x81bec.
Definition HW7B_E2 : Z := 0x81c08.
Definition HW7B_J : Z := 0x82618.
Lemma hw7b_strlen_entry : HW7B_STRLEN = STRLEN_ENTRY_B.
Proof. reflexivity. Qed.
(* the shadow base for the engine's shadow tokens: s11 holds K (the runtime's shadow offset), atom 27 *)
Definition HW7B_SB : Z := 0x7fff8000.
Definition hw7b_Bx : sv := SOff 27 0.
Definition hw7b_Bspan : Z * Z := (HW7B_SB, HW7B_SB + 2 ^ 44 - 1).
(* the param table entry's address, A1's a0 at 0x81b30: 0x9c600 + ((p & 7) << 3) (ent_headamp_key.param) *)
Definition HW7B_PTAB (p : Z) : Z := 0x9c600 + 8 * (p mod 8).
(* sep: "" (0x21240) when bit 7 of p is set, else "." (0x21460) (0x81b30 .. 0x81b48) *)
Definition hw7b_sep (p : Z) : Z := if Z.testbit p 7 then 0x21240 else 0x21460.
(* the key's fixed text "reac.headamp." (0x81b4c .. 0x81b50) *)
Definition HW7B_HPFX : Z := 0x20f40.

(* ---- the model of a case-0 turn (Model.ent_headamp_key on the bytes after the kind byte) ---- *)
(* the separator after the key's first part (pod.h:251) and the param name (pod.h:252) *)
Definition hw7b_sepb (p : Z) : list byte := if Z.testbit p 7 then [] else DOT.
Definition hw7b_pab (p : Z) : list byte := nth (Z.to_nat (p mod 8)) param [].
(* the key's text: the four parts joined; it is at most 13 + 21 + 1 + 9 = 44 bytes, so neither clamp cuts it *)
Definition hw7b_js (chs : list byte) (p : Z) : list byte := HPFX ++ chs ++ hw7b_sepb p ++ hw7b_pab p.
(* e62's 104 bytes at J: type 8 (POD_STRING), size |js| + 1, the text, its NUL, and the zeros of the memset *)
Definition hw7b_e62 (js : list byte) : list byte :=
le32 8 ++ le32 (Z.of_nat (length js) + 1) ++ js ++ [NUL] ++ zeros (95 - length js).

Lemma hw7b_wx : wx_segs_nowrap rsegs.
Proof. exact img_wx. Qed.
Lemma hw7b_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact img_segs_low. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- engine helpers [cgif lib/A/AC8j.v:43-78] ---- *)
Lemma hw7b_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma hw7b_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
Section d.
Variable B : asyms.
Lemma hw7b_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.

End d.

(* ---- memory facts that move with the memory [fuzz_role lib/A/RPgW7bKit.v w7_kept, w7_hull, w7_strok, w7_strz] ---- *)

Lemma hw7b_kept_trans : forall W m1 m2 m3 (Z1 Z2 Z3 : Z -> Prop),
cb_kept W m1 m2 Z1 -> cb_kept W m2 m3 Z2 -> (forall a, Z1 a \/ Z2 a -> Z3 a) -> cb_kept W m1 m3 Z3.
Proof.
intros W m1 m2 m3 Z1 Z2 Z3 H12 H23 Hz a Ha Hn.
rewrite (H23 a Ha (fun h => Hn (Hz a (or_intror h)))). exact (H12 a Ha (fun h => Hn (Hz a (or_introl h)))).
Qed.
Lemma hw7b_kept_mono : forall W m m' (Z1 Z2 : Z -> Prop), cb_kept W m m' Z1 -> (forall a, Z1 a -> Z2 a) ->
cb_kept W m m' Z2.
Proof. intros W m m' Z1 Z2 H Hz a Ha Hn. exact (H a Ha (fun h => Hn (Hz a h))). Qed.
Lemma hw7b_kept_refl : forall W m Zn, cb_kept W m m Zn.
Proof. intros W m Zn a _ _. reflexivity. Qed.

(* the two sources of a cb_strok fact (proved in HPgW7bKit.v): an image string as HPgBase.hd_cstr states it
   (hi_strs), and the key's first part in ch (F+0xa0, a frame object in scope at G, its bytes and NUL there) *)
Definition hw7b_strok_cstr_stmt : Prop :=
forall W m R x (l : list byte),
hd_cstr rsegs (w_H W) m x (hd_zbytes l) -> x + Z.of_nat (length l) < R - 2 * ESTACK -> (length l <= 64)%nat ->
cb_strok W m R x l.
Definition hw7b_strok_ch_stmt : Prop :=
forall W m R F (chs : list byte),
hd_fsh rsegs (w_H W) m F (hmu_sh true true false false false true false false) -> F mod 8 = 0 ->
in_app F 1024 -> F + 1024 <= R - 2 * ESTACK ->
(forall a, F + 0xa0 <= a < F + 0xb8 -> aview rsegs (w_H W) m a <> None) ->
hm_bytes rsegs (w_H W) m (F + 0xa0) (chs ++ [NUL]) -> Forall (fun b : byte => bv_unsigned b <> 0) chs ->
(length chs <= 21)%nat ->
cb_strok W m R (F + 0xa0) chs.

(* ===================================== the statements of the walk's parts =====================================
   Each part is proved in its own file (HPgW7bBlkA.v A1 / A2, HPgW7bBlkB.v B / C / D / E1, HPgW7bBlkE.v E2,
   HPgW7bKit.v the two call steps, HPgW7bIter.v one parts-loop turn); the assembly takes them by these names. *)
Section s.
Variable B : asyms.

(* A1, 0x81afc .. 0x81b2c: andi a0,s10,7; a1 := 0x9c600; slli a0,a0,3; not a2,a1; bgeu a2,a0 (the UBSan bound test,
   never failing: a0 <= 56); add a0,a1,a0; the shadow check of the 8-byte entry at a0 (srli a1,a0,3; add a1,a1,s11;
   lbu a1,0(a1); beqz a1 -> 0x81b30; j report). It ends at 0x81b30 with a0 the entry's address. *)
Definition hw7b_A1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 26 = w64 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (HW7B_PTAB p) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_G) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_A2 regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (HW7B_PTAB p))).

(* A2, 0x81b30 .. 0x81b94 (pod.h:250-253): slli s10,s10,0x38; bgez s10 -> a1 := 0x21460 ("."), else a1 := 0x21240
   (""); a2 := 0x20f40; sd a2,0x178(s1); the shadow check of the 8-byte store at R+0x180 (addi a2,s1,0x180; srli;
   add a2,a2,s11; lbu a2,0(a2); [ld a0,0(a0)]; beqz a2 -> 0x81b74; j report); mv s5,t1; li s10,0; sd s2,0x180(s1);
   sd a1,0x188(s1); sd a0,0x190(s1); addi s2,s1,0x178; ld s7,0(s2); mv a0,s7; jal strlen. *)
Definition hw7b_A2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p R s2v pa,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (HW7B_PTAB p) -> getr regs 27 = w64 SHADOW_OFF -> getr regs 26 = w64 p -> 0 <= p < 256 ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 s2v -> 0 <= s2v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (HW7B_PTAB p) 8 pa -> 0 <= pa < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (R + 0x180) 8 ->
(forall a, R + 0x178 <= a < R + 0x198 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_A2) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_STRLEN regs memc mdc [1; 10; 11; 12; 18; 21; 23; 26]%bv
(fun a => R + 0x178 <= a < R + 0x198)
(fun regs2 mem2 => getr regs2 1 = w64 HW7B_AFTER_STRLEN /\ getr regs2 10 = w64 HW7B_HPFX /\
 getr regs2 23 = w64 HW7B_HPFX /\ getr regs2 18 = w64 (R + 0x178) /\ getr regs2 21 = getr regs 6 /\
 getr regs2 26 = w64 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x178) 8 HW7B_HPFX /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x180) 8 s2v /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x188) 8 (hw7b_sep p) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x190) 8 pa)).

(* B, 0x81b98 .. 0x81bb8 (pod.h:255-257): mv s4,a0; add a0,a0,s10; li a1,0x5f; bgeu a1,a0 -> 0x81bac (taken:
   l <= 21, n <= 40); [sub s4,a1,s10]; add a0,s9,s10; mv a1,s7; mv a2,s4; jal memcpy. *)
Definition hw7b_B_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) l n x t,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 l -> 0 <= l <= 21 -> getr regs 26 = w64 n -> 0 <= n <= 40 ->
getr regs 23 = w64 x -> getr regs 25 = w64 t -> 0 <= t -> t + 0x80 <= 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_AFTER_STRLEN) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_MEMCPY regs memc mdc [1; 10; 11; 12; 20]%bv
(fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 HW7B_AFTER_MEMCPY /\ getr regs2 10 = w64 (t + n) /\ getr regs2 11 = w64 x /\
 getr regs2 12 = w64 l /\ getr regs2 20 = w64 l)).

(* C, 0x81bbc .. 0x81b94 (i = 0 .. 2): addi s2,s2,8; add s10,s4,s10; addi a0,s1,0x198; bne s2,a0 -> 0x81b8c (taken:
   s2 = R + 0x180 + 8 i); ld s7,0(s2); mv a0,s7; jal strlen. *)
Definition hw7b_C_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i : nat) R n l x',
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> (i < 3)%nat ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x178 + 8 * Z.of_nat i) -> getr regs 26 = w64 n -> getr regs 20 = w64 l ->
0 <= n <= 40 -> 0 <= l <= 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x180 + 8 * Z.of_nat i) 8 x' -> 0 <= x' < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_STRLEN regs memc mdc [1; 10; 18; 23; 26]%bv
(fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 HW7B_AFTER_STRLEN /\ getr regs2 10 = w64 x' /\ getr regs2 23 = w64 x' /\
 getr regs2 18 = w64 (R + 0x180 + 8 * Z.of_nat i) /\ getr regs2 26 = w64 (n + l))).

(* D, 0x81bbc .. 0x81be8 (i = 3): addi s2,s2,8; add s10,s4,s10; addi a0,s1,0x198; bne s2,a0 (not taken:
   s2 = R + 0x198); li a0,0x5f; bltu s10,a0 -> 0x81bd8 (taken: n + l <= 61); ld s7,0x118(s1); mv a0,s7; mv a1,s9;
   mv a2,s10; jal memcpy. *)
Definition hw7b_D_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R n l t eb,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x190) -> getr regs 26 = w64 n -> getr regs 20 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
getr regs 25 = w64 t ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 eb -> 0 <= eb < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_MEMCPY regs memc mdc [1; 10; 11; 12; 18; 23; 26]%bv
(fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 HW7B_AFTER_TEXT /\ getr regs2 10 = w64 eb /\ getr regs2 11 = w64 t /\
 getr regs2 12 = w64 (n + l) /\ getr regs2 23 = w64 eb /\ getr regs2 26 = w64 (n + l))).

(* E1, 0x81bec .. 0x81c04: ld s2,0x138(s1); ld s4,0x130(s1); ld a0,0xe8(s1); bgeu a0,s10 -> 0x81c00 (the UBSan
   bound test, never failing: a0 = ~(e62 + 8) >= 95 >= n); add a0,s7,s10; addi s10,s10,1. *)
Definition hw7b_E1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R eb n vlen ea vc,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 23 = w64 eb -> getr regs 26 = w64 n -> 0 <= eb -> 0 <= n <= 95 -> eb + n + 1 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 vlen -> 0 <= vlen < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ea -> 0 <= ea < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vc -> 95 <= vc < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_AFTER_TEXT) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_E2 regs memc mdc [10; 18; 20; 26]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (eb + n) /\ getr regs2 18 = w64 vlen /\ getr regs2 20 = w64 ea /\
 getr regs2 26 = w64 (n + 1))).

(* E2, 0x81c08 .. 0x81c64 (pod.h:258-262): sb zero,0(a0) (the NUL at xb = e62.body + n); li a0,8; sw a0,0(s4);
   sw s10,4(s4) (e62.type = 8, e62.size = n + 1 at ea = &e62); li a0,-8; 15 x sb a0 at s3 + 0x14 .. 0x16, 8 .. 0xb,
   4 .. 7, 0xc .. 0xf (ch and t out of scope: shadow bytes 0xf8 of the frame for locals sF); ld a3,0x110(s1);
   ld s7,0x148(s1); mv t1,s5; j 0x82618. *)
Definition hw7b_E2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R sF xb ea m lv vcur vpp,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 xb -> getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 19 = w64 sF -> getr regs 20 = w64 ea -> getr regs 26 = w64 m -> 0 <= m < 2 ^ 32 ->
getr regs 21 = w64 lv ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 vcur -> 0 <= vcur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 vpp -> 0 <= vpp < 2 ^ 64 ->
0 <= ea -> ea + 8 <= xb -> xb < R -> 0 <= sF -> (sF + 0x17 <= ea \/ xb < sF) -> sF + 0x17 <= R ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own xb ->
(forall a, ea <= a < ea + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
(forall a, (sF + 4 <= a < sF + 0x10 \/ sF + 0x14 <= a < sF + 0x17) ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_E2) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HW7B_J regs memc mdc [6; 10; 13; 23]%bv
(fun a => a = xb \/ ea <= a < ea + 8 \/ sF + 4 <= a < sF + 0x10 \/ sF + 0x14 <= a < sF + 0x17)
(fun regs2 mem2 => getr regs2 13 = w64 vcur /\ getr regs2 23 = w64 vpp /\ getr regs2 6 = w64 lv /\
 aview rsegs (w_H W) mem2 xb = Some 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) ea 4 8 /\ val_mem rsegs (mrestrict (w_H W) mem2) (ea + 4) 4 m /\
 (forall i, (4 <= i < 0x10 \/ 0x14 <= i < 0x17) -> aview rsegs (w_H W) mem2 (sF + i) = Some 0xf8))).

(* the runtime's memcpy (0x51d8c) in the journal form, keeping the I/O state [fuzz_role lib/A/RPgW7bKit.v
   w7_memcpy_at] *)
Definition hw7b_memcpy_at_stmt : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok rsegs W regsT memT x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 HW7B_MEMCPY) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = aview rsegs (w_H W) memT (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).

(* the strlen wrapper (0x41c18) in the journal form, keeping the I/O state, on a cb_strok string
   [fuzz_role lib/A/RPgW7bCall.v w7_strlen_at; w7_strlen_cstr is lib/A/HPgW7bCall.v's] *)
Definition hw7b_strlen_at_stmt : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x s (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
cb_strok W memT (sp0 + o) x s ->
aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 HW7B_STRLEN) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length s)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).

(* one turn of the parts loop (pod.h:254-257), from the strlen wrapper's entry (called at 0x81b94, ra = 0x81b98)
   to the return of memcpy(t + n, parts[i], l) (0x81bbc): strlen, block B, memcpy [fuzz_role lib/A/RPgW7bIter.v
   w7_iter]. s7 holds the part x, s10 the length so far n, s9 = t; after the turn s4 = l and the copied bytes are at
   t + n. *)
Definition hw7b_iter_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R t n x s
(Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 1 = w64 HW7B_AFTER_STRLEN -> getr regs 10 = w64 x -> getr regs 23 = w64 x ->
getr regs 26 = w64 n -> getr regs 25 = w64 t -> getr regs 2 = w64 R ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
R mod 16 = 0 -> sp0 mod 16 = 0 -> R <= sp0 -> 2 * ESTACK - (R - sp0) <= STK -> 2 * ESTACK <= R -> R < 2 ^ 63 ->
cb_strok W mem R x s -> aro_unowned rsegs B (aview rsegs (w_H W) mem) ->
(length s <= 21)%nat -> 0 <= n <= 40 -> 0 <= t -> t + 0x80 <= R - 2 * ESTACK ->
(forall a, t + n <= a < t + n + Z.of_nat (length s) -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
amem_range (t + n) (Z.of_nat (length s)) ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (t + n) (Z.of_nat (length s)) ->
(0 < Z.of_nat (length s) -> shadow_hull_vis (aview rsegs (w_H W) mem) (t + n) (Z.of_nat (length s))) ->
(forall a, cb_hull (t + n) (Z.of_nat (length s)) a -> 0 <= a < R - 2 * ESTACK) ->
(forall a, cb_strz x s a -> 0 <= a < R - 2 * ESTACK) ->
(t + n + Z.of_nat (length s) <= x \/ x + Z.of_nat (length s) <= t + n) ->
(forall regs2 mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io md md2 ->
 (forall r, acallee_saved r -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 getr regs2 20 = w64 (Z.of_nat (length s)) ->
 (forall j, (j < length s)%nat ->
  aview rsegs (w_H W) mem2 (t + n + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
 cb_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R \/ t + n <= a < t + n + Z.of_nat (length s)) ->
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 HW7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_STRLEN) mem (seg_rom rsegs)) md) Q.

(* ===================================== the walk G -> J over explicit facts =====================================
   The whole walk 0x81afc -> 0x82618 as one lemma over the explicit register, cell and byte facts it reads (the piece
   lemma of lib/AU/HPgW7b.v reads them off the cut G and rebuilds the cut J from the post), in the continuation form:
   for every state the walk can reach at J, with the journal and the I/O state kept, the callee-saved registers the
   cut J names kept, a3 := the cursor (R+0x110), s2 := &pp->len (R+0x138), s4 := &e62 (R+0x130), s7 := pp (R+0x148),
   t1 as at G, e62 holding the key's pod, the frame's shadow with t and ch out of scope again, and every byte outside
   the callees' stack [R - 2 ESTACK, R), parts[0 .. 3], t, e62 and the frame's 116 shadow bytes as at G, Q holds at J;
   then Q holds at G. Image B: R = s1 = sp, F the frame for locals (class 4, 1024 bytes), p (s10) the third byte of
   the head-amp key, chs the key's first part in ch (F+0xa0) with its NUL, pa = param[p mod 8]. *)
Definition hw7b_core_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  R F p chs pa vlen vcur vpp (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - T_SEG_STK -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
alloc_ceiling + T_SEG_STK <= R ->
F mod 32 = 0 -> 4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
(forall a, F <= a < F + 1024 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ aview rsegs (w_H W) memc a <> None /\
 ~ in_img rsegs a) ->
(forall i, 0 <= i < 116 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (shadow_addr F + i)) ->
(forall a, R + 0x178 <= a < R + 0x198 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 26 = w64 p -> 0 <= p < 256 ->
getr regs 25 = w64 (F + 0x20) -> getr regs 18 = w64 (F + 0xa0) -> getr regs 19 = w64 (shadow_addr F) ->
hd_fsh rsegs (w_H W) memc F (hmu_sh true true false false false true false false) ->
hm_bytes rsegs (w_H W) memc (F + 0xa0) (chs ++ [NUL]) -> Forall (fun b : byte => bv_unsigned b <> 0) chs ->
(length chs <= 21)%nat ->
hm_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104) ->
hd_cstr rsegs (w_H W) memc HW7B_HPFX (hd_zbytes HPFX) ->
hd_cstr rsegs (w_H W) memc (hw7b_sep p) (hd_zbytes (hw7b_sepb p)) ->
val_mem rsegs (mrestrict (w_H W) memc) (HW7B_PTAB p) 8 pa ->
hd_cstr rsegs (w_H W) memc pa (hd_zbytes (hw7b_pab p)) -> 0x20f40 <= pa <= 0x21460 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (HW7B_PTAB p) 8 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (R + 0x180) 8 ->
aro_unowned rsegs B (aview rsegs (w_H W) memc) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- F - 0x219) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 vlen -> 0 <= vlen < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 vcur -> 0 <= vcur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 vpp -> 0 <= vpp < 2 ^ 64 ->
(forall regs2 mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall r, In r [2; 3; 4; 8; 9; 19; 22; 24; 25; 27] -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 getr regs2 6 = getr regs 6 -> getr regs2 13 = w64 vcur -> getr regs2 18 = w64 vlen ->
 getr regs2 20 = w64 (F + 0x210) -> getr regs2 23 = w64 vpp ->
 hm_bytes rsegs (w_H W) mem2 (F + 0x210) (hw7b_e62 (hw7b_js chs p)) ->
 hd_fsh rsegs (w_H W) mem2 F (hmu_sh false false false false false true false false) ->
 cb_kept W memc mem2 (fun a => R - 2 * ESTACK <= a < R \/ R + 0x178 <= a < R + 0x198 \/
   F + 0x20 <= a < F + 0x80 \/ F + 0x210 <= a < F + 0x278 \/ shadow_addr F <= a < shadow_addr F + 116) ->
 (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 HW7B_J) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_G) memc (seg_rom rsegs)) mdc) Q.
End s.
End b.

Print Assumptions hw7b_tbl_ok.
Print Assumptions hw7b_kept_trans.
