(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), the strlen trampoline 0x41ac8 -> 0x41b98 and __asan_memcpy 0x510d4 -> 0x51d0c, the real-frame cells by the plan's slot map, RPgCfgChanges.cfg_wx / cfg_segs_low -> HPgSteps.img_wx / img_segs_low, and kept_run (RPgCfgChanges.v:78-86 at f3898085bda, over headamp's rsegs) added. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the shared pieces of the walk of
   LLVMFuzzerTestOneInput from 0x81a34 (ent_build case 0 after the digits, the reverse and the odd_ch part: pod.h:250)
   to 0x8237c (the pod built). Proves no function (kind: segment lemma).

   THE SPLIT. The walk is cut at every call and at the two places the engine cannot address a computed pointer:
     A1  0x81a34 -> 0x81a5c   the param table entry address and its shadow check (pod.h:250)
     A2  0x81a5c -> 0x41b98   sep, parts[0..3] stored at R+0x140.., the store check of parts[1], strlen(parts[0])
     B   0x81ac4 -> 0x51d0c   one turn's clamp and memcpy(t + n, parts[i], l)            (i = 0 .. 3)
     C   0x81ae8 -> 0x41b98   n += l, the next part, strlen(parts[i+1])                   (i = 0 .. 2)
     D   0x81ae8 -> 0x51d0c   n += l, the 95 clamp of ent_text, memcpy(e.body, t, n)        (i = 3)
     E1  0x81b18 -> 0x81b20   the NUL's address
     E2  0x81b20 -> 0x8237c   NUL, e.type = 8, e.size = n + 1, t and ch out of scope, the reloads, j J
   Every block is a lemma from the block's first pc to a fixed pc in the shape w7_post: the journal kept (no event),
   the world kept, the I/O state kept (same_io from the block's model), every register outside clob kept, every byte outside the block's write set Wr kept, every present
   byte present, and R. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code: the 85 words 0x81a34 .. 0x81b84 ---- *)
Definition W7_PC0 : Z := 0x81a34.
Definition w7_tbl : ctable := build_table rsegs W7_PC0 85 TEmpty.
Lemma w7_tbl_ok : table_ok rsegs w7_tbl.
Proof. apply build_table_ok0. unfold W7_PC0. lia. Qed.
(* the pcs the blocks start and end at *)
Definition W7_A2 : Z := 0x81a5c.
Definition W7_STRLEN : Z := 0x41b98.      (* __interceptor_trampoline_strlen, Rt/StrlenDef.v's STRLEN_ENTRY_A *)
Definition W7_MEMCPY : Z := 0x51d0c.      (* __asan_memcpy *)
Definition W7_AFTER_STRLEN : Z := 0x81ac4.
Definition W7_AFTER_MEMCPY : Z := 0x81ae8.
Definition W7_AFTER_TEXT : Z := 0x81b18.
Definition W7_E2 : Z := 0x81b20.
Definition W7_J : Z := 0x8237c.
(* the shadow base for the engine's shadow tokens: s7 holds K (the runtime's shadow offset), atom 23 *)
Definition W7SB : Z := 0x7fff8000.
Definition W7Bx : sv := SOff 23 0.
Definition W7Bspan : Z * Z := (W7SB, W7SB + 2 ^ 44 - 1).
(* sep: "" (.str.15 0x21200) when bit 7 of p is set, else "." (.str.31 0x21420) (0x81a5c .. 0x81a74) *)
Definition w7_sep (p : Z) : Z := if Z.testbit p 7 then 0x21200 else 0x21420.

Lemma w7_wx : wx_segs_nowrap rsegs.
Proof. exact HPgSteps.img_wx. Qed.
Lemma w7_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact HPgSteps.img_segs_low. Qed.

(* a run that writes only inside its regions' write ranges keeps every byte outside Zn that the step before it kept *)
Lemma kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- engine helpers [cgif lib/A/AC8j.v:43-78] ---- *)
Lemma w7_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w7_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
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
Lemma w7_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.

(* ---- the 31 registers other than x0; a register whose symbolic value is still its own atom kept its value ---- *)
Definition w7_nz_regs : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma w7_in_nz_regs : forall r : bv 5, bv_unsigned r <> 0 -> In r w7_nz_regs.
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
repeat (destruct H as [H|H]; [rewrite H; cbv [w7_nz_regs In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
rewrite H. cbv [w7_nz_regs In]. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma w7_regs_kept : forall E ss ms regs0 extra (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) w7_nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H clob HS [HA _] Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (w7_in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the block post ---- *)
Definition w7_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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

(* the leaf of a block: the engine's last state, at the block's end pc, gives w7_post *)
Lemma w7_post_of_run : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
R (ms_regs ms) (ms_mem ms) ->
SRr rsegs W (mkCfg ms md) (w7_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md HS Hrv Hpc HJ Hio Hregs Hkept Hgr HR.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hregs|]. split; [exact Hkept|].
split; [intros a Ha; exact (apresent_grows (w_H W) memc (ms_mem ms) a Hgr Ha) | exact HR].
Qed.
End d.
End b.
