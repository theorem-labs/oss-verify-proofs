(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the code table (87 words from 0x8150c), the block pcs, the strlen and memcpy entries, the two separators and the shadow token's base register (s2, atom 18) are rate's; the image facts come from lib/A/RtPgSteps.v; kept_run of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 25d4b718638e is added as w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBase.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the code table (90 words from 0x8160c), the block pcs, the strlen and memcpy entries and the shadow token's base register (s4, atom 20) are image B's; the split gains the two UBSan trap branches 0x81620 and 0x81708 and E1 the three cell reloads; the image facts come from lib/AU/RtPgStepsB.v; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, which holds the same loaded bytes): the shared
   pieces of the walk of LLVMFuzzerTestOneInput from G 0x8160c (ent_build case 0 after the digits, the reverse and
   the odd_ch part: pod.h:250) to J 0x820dc (the pod built). Proves no function (kind: segment lemma).

   THE SPLIT. The walk is cut at every call and at the two places the engine cannot address a computed pointer:
     A1  0x8160c -> 0x81640   the param table entry address, its UBSan pointer-overflow test (`not a2,a1; bgeu a2,a0`
                              0x8161c / 0x81620, the other arm `j` 0x83098) and its shadow check (pod.h:250)
     A2  0x81640 -> 0x421ec   sep, parts[0..3] stored at R+0x198.., the store check of parts[1], strlen(parts[0])
     B   0x816a8 -> 0x518b8   one turn's clamp and memcpy(t + n, parts[i], l)            (i = 0 .. 3)
     C   0x816cc -> 0x421ec   n += l, the next part, strlen(parts[i+1])                   (i = 0 .. 2)
     D   0x816cc -> 0x518b8   n += l, the 95 clamp of ent_text, memcpy(e62.body, t, n)      (i = 3)
     E1  0x816fc -> 0x81718   the reloads of &pp->len and &e62, the UBSan test of e62.body + n (`ld a0,0x100(s1);
                              bgeu a0,s9` 0x81704 / 0x81708, the cell holding ~(F + 0x218)), the NUL's address
     E2  0x81718 -> 0x820dc   NUL, e62.type = 8, e62.size = n + 1, t and ch out of scope, the cursor's reload, `j` J
   The registers (image B's measured map): s4 = K (the runtime's shadow offset, atom 20), s3 = the frame's shadow
   base, s11 = &t, s2 = the part pointer (&ch at G), s8 = the saved input left (t1 at G, back in t1 at J),
   s10 = the part's string, s9 = p at G and then n, s6 = the length of the part.
   Every block is a lemma from the block's first pc to a fixed pc in the shape w7b_post: the journal kept (no event),
   the world kept, the I/O state kept (same_io from the block's model), every register outside clob kept, every
   byte outside the block's write set Wr kept, every present byte present, and R. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ---- the code: the 90 words 0x8160c .. 0x81770 ---- *)
Definition W7B_PC0 : Z := 0x8160c.
Definition w7b_tbl : ctable := build_table rsegs W7B_PC0 90 TEmpty.
Lemma w7b_tbl_ok : table_ok rsegs w7b_tbl.
Proof. apply build_table_ok0. unfold W7B_PC0. lia. Qed.
(* the pcs the blocks start and end at *)
Definition W7B_A2 : Z := 0x81640.
Definition W7B_STRLEN : Z := 0x421ec.      (* the strlen wrapper, the `jal` target at 0x816a4 *)
Definition W7B_MEMCPY : Z := 0x518b8.      (* __asan_memcpy, the `jal` target at 0x816c8 and 0x816f8 *)
Definition W7B_AFTER_STRLEN : Z := 0x816a8.
Definition W7B_AFTER_MEMCPY : Z := 0x816cc.
Definition W7B_AFTER_TEXT : Z := 0x816fc.
Definition W7B_E2 : Z := 0x81718.
Definition W7B_J : Z := 0x820dc.
(* the shadow base for the engine's shadow tokens: s4 holds K (the runtime's shadow offset), atom 20 *)
Definition W7B_SB : Z := 0x7fff8000.
Definition W7B_Bx : sv := SOff 20 0.
Definition W7B_span : Z * Z := (W7B_SB, W7B_SB + 2 ^ 44 - 1).
(* sep: "" (.str.17 0x212e0) when bit 7 of p is set, else "." (.str.33 0x21500) (0x81640 .. 0x81658) *)
Definition w7b_sep (p : Z) : Z := if Z.testbit p 7 then 0x212e0 else 0x21500.

Lemma w7b_wx : wx_segs_nowrap rsegs.
Proof. exact RtPgStepsB.rtsb_wx. Qed.
Lemma w7b_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact RtPgStepsB.rtsb_segs_low. Qed.
Lemma w7b_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. exact RtPgStepsB.same_io_wvb. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- engine helpers [cgif lib/A/AC8j.v:43-78] ---- *)
Lemma w7b_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w7b_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* a run keeps every byte outside the zone its write windows lie in [role lib/A/RPgCfgChanges.v kept_run] *)
Lemma w7b_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Section d.
Variable B : asyms.
Lemma w7b_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.

(* ---- the 31 registers other than x0; a register whose symbolic value is still its own atom kept its value ---- *)
Definition w7b_nz_regs : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma w7b_in_nz_regs : forall r : bv 5, bv_unsigned r <> 0 -> In r w7b_nz_regs.
Proof.
intros r Hr. pose proof (u5_range r) as Hb.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (H : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/
  bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/
  bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
  bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/
  bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
  bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/
  bv_unsigned r = 31) by lia.
repeat (destruct H as [H|H]; [rewrite H; cbv [w7b_nz_regs In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
rewrite H. cbv [w7b_nz_regs In]. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma w7b_regs_kept : forall E ss ms regs0 extra (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) w7b_nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H clob HS [HA _] Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (w7b_in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the block post ---- *)
Definition w7b_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (pc : Z) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (clob : list (bv 5))
(Wr : Z -> Prop) (R : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
R regs2 mem2.

(* the leaf of a block: the engine's last state, at the block's end pc, gives w7b_post *)
Lemma w7b_post_of_run : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
R (ms_regs ms) (ms_mem ms) ->
SRr rsegs W (mkCfg ms md) (w7b_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md HS Hrv Hpc HJ Hio Hregs Hkept Hgr HR.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hregs|]. split; [exact Hkept|].
split; [intros a Ha; exact (apresent_grows (w_H W) memc (ms_mem ms) a Hgr Ha) | exact HR].
Qed.
End d.
End b.

Print Assumptions w7b_post_of_run.
Print Assumptions w7b_regs_kept.
Print Assumptions w7b_kept_run.
