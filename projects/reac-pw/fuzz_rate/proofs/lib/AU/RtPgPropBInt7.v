(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v at 533bf30ff015 for image B (fuzz_rate.asan-ubsan): image B's block SEL7 0x80ff4 -> LATCH7 0x8257c (e into scope, memset(e.body, 0, 96) through lib/AU/RtPgStepsB.v rtsb_intrin_at at 0x51d54, e.size = e.type = 4, the call pod_write_ent(pp, e) 0x81054 through rtsb_pwe_at with lib/AU/PweSpec.v's contract at 0x83cc4 as a Section hypothesis, e out of scope) in three engine runs over the kit lib/AU/RtPgPropBKit.v, with the frame shadow, frame-object and record facts of lib/AU/RtPgMemB.v; the piece is lib/AU/RtPgSegB.v's rsb_piece_W4_int7_stmt with image B's cut lists. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the shape-7 Int pod block SEL7
   0x80ff4 -> LATCH7 0x8257c of LLVMFuzzerTestOneInput, as a block lemma over lib/AU/RtPgPropBKit.v, and the piece
   rsb_piece_W4_int7_stmt of lib/AU/RtPgSegB.v. Proves no function (kind: segment lemma).

   THE BLOCK (pod.h:403-405: struct pod_ent e = {4, 4, {0}}; pod_write_ent(pp, &e))
     0x80ff4 .. 0x81024   the 13 stores `sb zero, 30..42(s3)`: e (F + 0xf0, 104 bytes, granules 30 .. 42) into scope.
     0x81028 .. 0x8103c   a2 = 96, a0 = e.body (R+0xb8 = F + 0xf8), a1 = 0, s2 = t0 (the property index), s8 = t4
                          (what is left of the input), `jal 0x51d54` (__asan_memset(F + 0xf8, 0, 96), ra = 0x81040).
     0x81040 .. 0x81054   a1 = &e (R+0xd0 = F + 0xf0), e.size = e.type = 4 (two `sw` without a check), a0 = pp
                          (R+0x168), `jal 0x83cc4` (pod_write_ent(pp, &e), ra = 0x81058).
     0x81058 .. 0x810a0   t4 = s8, t0 = s2, the 13 stores `sb -8, 30..42(s3)` (e out of scope), s8 = -8, a3 = s6
                          (seen), `j 0x8257c`.
   ROUTE. Three runs of the kit's engine without shadow tokens (lib/Reusable/YCbq.v aj_run_to: no branch and no
   instrumented check is on the path, and the token run refuses a write window inside the shadow band), each from an
   entry state with only the regions it reads or writes and no atom fact: 0x80ff4 to the memset entry 0x51d54 (the frame's
   shadow window [shadow_addr F + 30, + 43) at atom 19 = s3, and R+0xb8), 0x81040 to pod_write_ent's entry 0x83cc4
   (R+0xd0, R+0x168, and e's header window [F + 0xf0, F + 0xf8) at the extra atom 33 = F), and 0x81058 to 0x8257c
   (the shadow window again). Between them the two calls: __asan_memset's contract (Section hypothesis AMEMSET)
   through RtPgStepsB.rtsb_intrin_at, and pod_write_ent's (Section hypothesis PWE) through rtsb_pwe_at; the call
   premises on e (its 104 bytes are Layout.ent_mem of the ent {4, 4, [0; 0; 0; 0]}, addressable and with a readable
   shadow hull while e is in scope) come from the shadow bytes the first run wrote (RtPgMemB rtmb_sh_e_in,
   rtmb_B_ra_e). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB RtPgMemB PweSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgPropBKit RtPgPropBLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the statement's constants ---- *)
Definition PAB_I7_MEMSET : Z := 0x51d54.
Definition PAB_I7_RET1 : Z := 0x81040.
(* the ent the block hands pod_write_ent: type POD_INT, size 4, body the four bytes of the int 0 (pod.h:403) *)
Definition pab_e7 : Model.ent := Model.Ent Model.POD_INT 4 (le32 0).
(* the registers the block may change: the two calls' caller-saved set, s2 (the index across the calls) and s8
   (what is left of the input across the calls, then -8) *)
Definition pab_i7_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 24; 28; 29; 30; 31]%bv.
(* the registers each run changes *)
Definition pab_i7_clobA : list (bv 5) := [1; 10; 11; 12; 18; 24]%bv.
Definition pab_i7_clobB : list (bv 5) := [1; 10; 11]%bv.
Definition pab_i7_clobC : list (bv 5) := [5; 10; 13; 24; 29]%bv.
(* the bytes the block may write: e's 104 bytes, its 13 shadow bytes, the 16 bytes pod_write_ent puts at pp + plen and
   the len cell, and the two callees' stack below R *)
Definition pab_i7_Wr (R F pp plen : Z) (a : Z) : Prop :=
F + 0xf0 <= a < F + 0x158 \/ shadow_addr F + 30 <= a < shadow_addr F + 43 \/
pp + plen <= a < pp + plen + 16 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R - T_pwe_STK <= a < R.
(* two intervals apart (kept folded, so that lia does not split on it unless asked) *)
Definition pab_i7_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

(* ---- the three engine states ---- *)
(* the frame's shadow bytes of e (granules 30 .. 42) at atom 19 = s3 = shadow_addr F *)
Definition pab_i7_SH : YP09.region := YP09.mkRegion (Some 19%nat) 30 43 30 43 [].
Definition pab_i7_G0 : facts := mkFacts [] [] [].
(* 0x80ff4: atom 9 = R, 19 = shadow_addr F, 33 = F; the cell R+0xb8 = F + 0xf8 *)
Definition pab_i7_RA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0 0 [YP09.mkChunk 0xb8 (CVal 8 (SOff 33 0xf8))].
Definition pab_i7_ssA : sstate := mkSS PAB_SEL7 sr_atoms [pab_i7_RA; pab_i7_SH] None pab_i7_G0.
(* 0x81040: atom 9 = R, 33 = F, 34 = pp; the cells R+0xd0 = F + 0xf0 and R+0x168 = pp; e's header [F + 0xf0, + 8) *)
Definition pab_i7_RB : YP09.region := YP09.mkRegion (Some 9%nat) 0xd0 0x170 0 0
  [YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0xf0)); YP09.mkChunk 0x168 (CVal 8 (SOff 34 0))].
Definition pab_i7_EH : YP09.region := YP09.mkRegion (Some 33%nat) 0xf0 0xf8 0xf0 0xf8 [].
Definition pab_i7_ssB : sstate := mkSS PAB_I7_RET1 sr_atoms [pab_i7_RB; pab_i7_EH] None pab_i7_G0.
(* 0x81058: atom 19 = shadow_addr F *)
Definition pab_i7_ssC : sstate := mkSS PWE_RA_SHAPE7 sr_atoms [pab_i7_SH] None pab_i7_G0.

(* ---- the ent and its bytes ---- *)
Lemma pab_e7_len : pwe_len pab_e7 = 16.
Proof. vm_compute. reflexivity. Qed.
Lemma pab_e7_len' : Z.of_nat (length (Model.enc_pod pab_e7)) = 16.
Proof. vm_compute. reflexivity. Qed.
Lemma pab_e7_enc : Model.enc_pod pab_e7 = prop_bytes 7 (0, PInt 0).
Proof. vm_compute. reflexivity. Qed.
Lemma pab_e7_mem : Layout.ent_mem pab_e7 =
  [Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
  ++ repeat (Z_to_bv 8 0) 96.
Proof. vm_compute. reflexivity. Qed.

(* ---- arithmetic ---- *)
Lemma pab_i7_mod16_sub : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. rewrite (Z.div_mod a 16) by lia. rewrite (Z.div_mod b 16) by lia. rewrite Ha, Hb, !Z.add_0_r.
replace (16 * (a / 16) - 16 * (b / 16)) with ((a / 16 - b / 16) * 16) by ring. apply Z.mod_mul. lia.
Qed.
Lemma pab_i7_floor8 : forall x, x - 7 <= x / 8 * 8 <= x.
Proof.
intros x. pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M. lia.
Qed.

(* ---- values of symbolic terms ---- *)
Lemma pab_i7_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma pab_i7_den0 : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof.
intros E n w H. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
unfold zcanon, M64. apply Z.mod_small. exact Rw.
Qed.

(* ---- registers ---- *)
Lemma pab_i7_notin : forall (l : list (bv 5)) r, existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros l r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) l = true).
{ apply existsb_exists. exists r. split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]. }
rewrite H in Ht. discriminate Ht.
Qed.
Lemma pab_i7_incl : forall l1 l2 : list (bv 5),
forallb (fun c => existsb (fun d => bv_eqb d c) l2) l1 = true -> forall r, ~ In r l2 -> ~ In r l1.
Proof.
intros l1 l2 H r Hn Hin. apply Hn. rewrite forallb_forall in H. specialize (H r Hin).
apply existsb_exists in H as (d & Hd & Hb). apply bv_eqb_eq in Hb. subst d. exact Hd.
Qed.
Lemma pab_i7_sub_cs : forallb (fun c => existsb (fun d => bv_eqb d c) pab_i7_clob) rtsb_caller_saved = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pab_i7_sub_A : forallb (fun c => existsb (fun d => bv_eqb d c) pab_i7_clob) pab_i7_clobA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pab_i7_sub_B : forallb (fun c => existsb (fun d => bv_eqb d c) pab_i7_clob) pab_i7_clobB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pab_i7_sub_C : forallb (fun c => existsb (fun d => bv_eqb d c) pab_i7_clob) pab_i7_clobC = true.
Proof. vm_compute. reflexivity. Qed.
(* across a call: a register outside the caller-saved set is kept *)
Lemma pab_i7_pres : forall (r0 r1 : bvmap 5 word) (r : bv 5), aregs_preserved r0 r1 ->
bv_unsigned r <> 0 -> ~ In r rtsb_caller_saved -> getr r1 r = getr r0 r.
Proof.
intros r0 r1 r HP Hr Hn. pose proof (HP (bv_unsigned r) (rtsb_callee r Hr Hn)) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
(* the two side conditions of a kept literal register *)
Ltac pab_i7_side :=
first [ (let Hz := fresh "Hz" in intro Hz; vm_compute in Hz; discriminate Hz)
      | (apply pab_i7_notin; vm_compute; reflexivity) ].

Section k. Context {fx : YK11.FPState}.
(* a register whose symbolic value at the end of a run is the one it had at the entry kept its value *)
Lemma pab_i7_regs_kept : forall E ss ms regs0 sr0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 sr0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. apply HR.
Qed.
(* a byte of a literal chunk of a region *)
Lemma pab_i7_lit : forall E H mem (k : nat) b lo hi wlo whi cs o (w : N) z i,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = b ->
In (YP09.mkChunk o (CVal w (SLit z))) cs -> 0 <= i < Z.of_N w ->
aview rsegs H mem (b + o + i) = Some (Z.shiftr (z mod 2 ^ 64) (8 * i) mod 2 ^ 8).
Proof.
intros E H mem k b lo hi wlo whi cs o w z i (_ & _ & _ & Hcs) Hb Hin Hi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
destruct (Hck i Hi) as (bb & Hb1 & Hm1).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hm1. injection Hb1 as <-.
unfold aview. rewrite Hm1. cbn [option_map]. f_equal.
all: unfold byte_of_word; cbn [sv_denot]; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with (2 ^ 8); change (bv_modulus 64) with (2 ^ 64); reflexivity.
Qed.
(* every byte outside a run's write windows is kept *)
Lemma pab_i7_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
End k.

(* the shadow hull of an object of the frame for locals at F + o (o >= 56) lies among the frame's known shadow bytes *)
Lemma pab_i7_hull : forall {fx : YK11.FPState} {rc : YM05.RunCeil} H mem F pat o n,
rt_fsh rsegs H mem F pat -> F mod 32 = 0 -> 56 <= o -> 0 < n -> o + n <= 8 * Z.of_nat (length pat) - 64 ->
shadow_hull_vis (aview rsegs H mem) (F + o) n.
Proof.
intros fx rc H mem F pat o n P HF Ho Hn Hl s Hs.
replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by ring.
rewrite (rtsb_fsh_addr F o HF) in Hs by lia. rewrite (rtsb_fsh_addr F (o + n - 1) HF) in Hs by lia.
pose proof (pab_i7_floor8 (shadow_addr F + o / 8)) as L1.
pose proof (pab_i7_floor8 (shadow_addr F + (o + n - 1) / 8)) as L2.
pose proof (Z.div_mod o 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (o + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (o + n - 1) 8 ltac:(lia)) as M2.
replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
rewrite (P (s - shadow_addr F)) by lia. discriminate.
Qed.

(* the shadow of a class-4 frame below the ceiling is no application byte *)
Lemma pab_i7_sh_apart : forall {rc : YM05.RunCeil} F lo len,
4096 <= F -> F + 1024 <= alloc_ceiling -> in_app lo len -> 0 <= len ->
pab_i7_apart lo len (shadow_addr F) 128.
Proof.
intros rc F lo len H1 H2 Ha Hl. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
unfold pab_i7_apart, in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* the value of register r at the end of a run *)
Ltac pab_i7_reg HS r Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hn : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg sg Hh E ss ms r HS)
end.
(* region i of the state at the end of a run *)
Ltac pab_i7_regn HS i Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
assert (Hn : region_ok sg E (mrestrict Hh (ms_mem ms)) rg)
  by (apply (rtsb_region_nth E ss ms i rg Hh HS); vm_compute; reflexivity)
end end.
(* a byte b + o + i of a literal chunk at offset o of the region Rg (base atom value b) *)
Ltac pab_i7_lit_tac Rg Eu :=
lazymatch goal with |- aview _ _ _ (?b + ?o + ?i) = _ =>
  rewrite (pab_i7_lit _ _ _ _ b _ _ _ _ _ o _ _ i Rg Eu
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(cbn; lia)) end.

(* the frame for locals has the same address at every layout of the journal *)
Section fa. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Lemma pab_i7_faddr : forall STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k1 ly2 S2 W2 mem2 md2 k2 cid pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k1 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k1 ly2 S2 W2 mem2 md2 k2 cid pos (_ & L1 & _) (_ & L2 & _).
destruct L1 as (_ & _ & _ & _ & _ & E1 & _). destruct L2 as (_ & _ & _ & _ & _ & E2 & _).
unfold frame_addr. rewrite E1, E2. reflexivity.
Qed.
End fa.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the relation pod_write_ent_specX concludes at the block's call *)
Definition pab_i7_pwR (W : world rsegs) (memc : word -> option byte) (pp len q : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 _ mem2 =>
garr8 rsegs (mrestrict (w_H W2) mem2) (pp + len) (map (fun x : byte => bv_unsigned x) (Model.enc_pod pab_e7)) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + Layout.OFF_LEN) 8 (len + pwe_len pab_e7) /\
(forall x, 0 <= x < kHighMemEnd ->
 aview rsegs (w_H W2) mem2 (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x)) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF pp Layout.PP_SIZE /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF q Layout.ENT_SIZE.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51d54.
Hypothesis PWE : pod_write_ent_specX rsegs B MT 0x83cc4.

(* what the block computes, at LATCH7: t0 and t4 as at its start, s8 = -8, a3 = seen (s6), the frame's shadow
   back to rsb_P0, the 16 bytes pod_write_ent put at pp + plen and len = plen + 16 *)
Lemma pab_int7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pp plen pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> st_nev S + k <= EV_MAX ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
sp0 - STK + T_SEG_STK <= R -> R + 0x220 <= sp0 -> R mod 16 = 0 -> sp0 <= 2 ^ 47 -> alloc_ceiling + T_SEG_STK <= R ->
In (4, pos) own -> frame_addr lyc 4 pos = F -> F mod 32 = 0 -> in_app F 1024 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (F + 0xf8) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 (F + 0xf0) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen -> plen + 16 <= 5440 -> plen mod 8 = 0 ->
rt_fsh rsegs (w_H W) memc F rsb_P0 ->
SRr rsegs W (cfg_at rsegs PAB_SEL7 regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc PAB_LATCH7 pab_i7_clob
 (pab_i7_Wr R F pp plen)
 (fun W2 regs2 mem2 => getr regs2 5 = getr regs 5 /\ getr regs2 29 = getr regs 29 /\
   getr regs2 24 = w64 (-8) /\ getr regs2 13 = getr regs 22 /\
   rt_fsh rsegs (w_H W2) mem2 F rsb_P0 /\
   rtmb_bytes rsegs (w_H W2) mem2 (pp + plen) (prop_bytes 7 (0, PInt 0)) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (plen + 16))).
Proof using MTL LAWS AMEMSET PWE.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp plen pos
HJ Hev H2 H3 H4 H9 H19 HRlo HRhi HR16 Hsp47 HRceil Hown HFA HF32 HFapp Hpp Hpp0 Hsep0 Vb8 Vd0 V168 Vlen
Hp0 Hp16 Hp8 Hfsh0.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct ((al_blocks _ _ LAWS) lyc Sc W memc mdc pp Layout.PP_SIZE HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & _).
assert (Hrq : req_size Layout.PP_SIZE = 19744) by reflexivity.
rewrite Hrq in Hppceil, Hppapp.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (rtsb_fbounds F HF32 HFapp) as (HF4096 & HFceil & Hsh0 & HshC & HFsh0 & HFamr).
assert (HFsh : pab_i7_apart F 1024 (shadow_addr F) 128) by exact HFsh0. clear HFsh0.
assert (Hsep : pab_i7_apart pp 19744 F 1024) by exact Hsep0. clear Hsep0.
assert (Hppsh : pab_i7_apart pp 19744 (shadow_addr F) 128) by (apply pab_i7_sh_apart; [lia | lia | exact Hppapp | lia]).
pose proof (rtsb_fmod8 F 0 HF32) as FB8. rewrite Z.mul_0_r, Z.add_0_r in FB8.
unfold T_SEG_STK, ASTACK in HRlo, HRceil.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HTP : T_pwe_STK = 4144) by reflexivity.
destruct ((al_frames _ _ LAWS) lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & _ & HFSpres0).
rewrite HFA in HFSpres0. change (fs_frame_bytes 4) with 1024 in HFSpres0. change (1024 / 8) with 128 in HFSpres0.
(* ---- the entry state at 0x80ff4 ---- *)
set (EA := Ereg regs (pab_extra [F])).
assert (E9 : ew EA 9 = Z_to_bv 64 R) by (subst EA; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew EA 19 = Z_to_bv 64 (shadow_addr F)) by (subst EA; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E33 : ew EA 33 = Z_to_bv 64 F) by reflexivity.
assert (E5 : ew EA 5 = getr regs 5) by (subst EA; apply ew_Ereg_nat; reflexivity).
assert (E29 : ew EA 29 = getr regs 29) by (subst EA; apply ew_Ereg_nat; reflexivity).
assert (E9u : bv_unsigned (ew EA 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew EA 19) = shadow_addr F) by (rewrite E19; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EA 33) = F) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok EA sr_atoms regs) by (subst EA; apply regs_ok_Ereg).
assert (HSA : st_ok rsegs EA pab_i7_ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 PAB_SEL7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); change (Ereg regs (pab_extra [F])) with EA.
  - exact HR0.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rtmb_ro_region rsegs EA (w_H W) memc 9 R); [exact E9u | lia | lia |].
      constructor; [|constructor].
      apply (pab_chunk8 EA _ R 0xb8 (SOff 33 0xf8) (F + 0xf8)); [apply pab_i7_soff; exact E33 | lia | exact Vb8].
    + apply (rtmb_rw_region rsegs EA (w_H W) memc 19 (shadow_addr F)); [exact E19u | lia | lia | | constructor].
      intros o Ho. exact (proj1 (HFSpres0 o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val pab_i7_RA pab_i7_SH]. rewrite E9u, E19u. lia.
  - split; [exact I | split; exact I]. }
clearbody EA.
unfold cfg_at. change (w64 PAB_SEL7) with (Z_to_bv 64 PAB_SEL7).
(* ---- 0x80ff4 .. 0x8103c, to the memset entry 0x51d54 ---- *)
aj_run_to pab_tbl_ok HSA HJ PAB_I7_MEMSET.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rtsb_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat pos);
    [reflexivity | rewrite E19u, HFA; reflexivity | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HSx : st_ok _ EA _ (restrict _ ?m) |- _ => rename m into msA end.
lazymatch goal with HFx : frame_of EA _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into FRA end.
pab_i7_reg HSA (1%bv : bv 5) RA1. pab_i7_reg HSA (10%bv : bv 5) RA10. pab_i7_reg HSA (11%bv : bv 5) RA11.
pab_i7_reg HSA (12%bv : bv 5) RA12. pab_i7_reg HSA (18%bv : bv 5) RA18. pab_i7_reg HSA (24%bv : bv 5) RA24.
assert (KRA : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clobA -> getr (ms_regs msA) r = getr regs r).
{ exact (pab_i7_regs_kept EA _ msA regs sr_atoms (w_H W) pab_i7_clobA HSA HR0 ltac:(vm_compute; reflexivity)). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 30 <= a < shadow_addr F + 43) ->
  aview rsegs (w_H W) (ms_mem msA) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. apply (pab_i7_keep_run EA (ss_mem pab_i7_ssA) (w_H W) memc (ms_mem msA)
    (fun x => shadow_addr F + 30 <= x < shadow_addr F + 43) FRA); [| exact Ha | exact Hn].
  intros x (r & Hr & Hb). cbv [pab_i7_ssA ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pab_i7_RA pab_i7_SH] in Hb;
    rewrite ?E9u, ?E19u in Hb; lia. }
pab_i7_regn HSA 1%nat RgSA.
assert (SHA : forall i, 30 <= i < 43 -> aview rsegs (w_H W) (ms_mem msA) (shadow_addr F + i) = Some 0).
{ intros i Hi. replace (shadow_addr F + i) with (shadow_addr F + i + 0) by ring.
  assert (Hc : i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/
    i = 40 \/ i = 41 \/ i = 42) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
  pab_i7_lit_tac RgSA E19u; vm_compute; reflexivity. }
(* the frame's shadow after the 13 stores: e in scope *)
assert (FSA : rt_fsh rsegs (w_H W) (ms_mem msA) F (rtmb_sh false false false true false false false)).
{ rewrite <- (rtmb_sh_e_in false false false false false false false).
  apply (rtmb_fsh_set rsegs (w_H W) memc (w_H W) (ms_mem msA) F rsb_P0 30 13 0 Hfsh0).
  - intros i Hi. change (Z.of_nat 30) with 30 in Hi. change (Z.of_nat (30 + 13)) with 43 in Hi. apply SHA. lia.
  - intros i Hi Hn. replace (Z.of_nat (length rsb_P0)) with 88 in Hi by reflexivity.
    change (Z.of_nat 30) with 30 in Hn. change (Z.of_nat (30 + 13)) with 43 in Hn.
    apply KA; lia. }
pose proof (proj1 HJ) as HARA.
assert (KA2 : getr (ms_regs msA) 2 = getr regs 2) by (apply KRA; pab_i7_side).
assert (KA3 : getr (ms_regs msA) 3 = getr regs 3) by (apply KRA; pab_i7_side).
assert (KA4 : getr (ms_regs msA) 4 = getr regs 4) by (apply KRA; pab_i7_side).
pose proof (rtmb_B_ra_e rsegs (w_H W) (ms_mem msA) F false false false false false false 8 96 FSA FB8
  ltac:(lia) ltac:(lia)) as RAd.
unfold RTMB_E in RAd. replace (F + 0xf0 + 8) with (F + 0xf8) in RAd by lia.
pose proof (pab_i7_hull (w_H W) (ms_mem msA) F _ 0xf8 96 FSA HF32 ltac:(lia) ltac:(lia)
  ltac:(rewrite rtmb_sh_len; change (Z.of_nat 88) with 88; lia)) as HULLd.
rewrite (st_ok_restrict_mkst rsegs (w_H W) EA _ msA HSA eq_refl) at 1.
(* ---- the call: __asan_memset(F + 0xf8, 0, 96), ra = 0x81040 ---- *)
eapply SRr_bind.
{ apply (rtsb_intrin_at B LAWS OSet PAB_I7_MEMSET AMEMSET W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc _ k (F + 0xf8) 0 96 (R - sp0) (Z_to_bv 64 PAB_I7_RET1) HJ).
  - rewrite RA10, (pab_i7_soff EA 33 F 248 E33). reflexivity.
  - rewrite RA11. reflexivity.
  - rewrite RA12. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite KA2, H2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - apply pab_i7_mod16_sub; assumption.
  - lia.
  - rewrite HES. lia.
  - rewrite KA3. exact H3.
  - rewrite KA4. exact H4.
  - rewrite RA1. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + apply (rtsb_awr_fobj _ _ _ _ _ _ _ pos a Hown). rewrite HFA. lia.
    + rewrite HES. lia.
  - apply HFamr; lia.
  - exact RAd.
  - intros _. exact HULLd.
  - exact I. }
cbv beta. intros Wm cm _ (-> & regsm & memm & mdm & -> & HJm & HPm & Hsmm & H10m & Heffm & Hfrm).
assert (KRm : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clob -> getr regsm r = getr regs r).
{ intros r Hr0 Hn. rewrite (pab_i7_pres _ _ r HPm Hr0 (pab_i7_incl _ _ pab_i7_sub_cs r Hn)).
  exact (KRA r Hr0 (pab_i7_incl _ _ pab_i7_sub_A r Hn)). }
assert (M18 : getr regsm 18 = getr regs 5).
{ transitivity (getr (ms_regs msA) 18); [exact (HPm 18 ltac:(unfold acallee_saved; lia)) |].
  rewrite RA18. exact (pab_i7_den0 EA 5 _ E5). }
assert (M24 : getr regsm 24 = getr regs 29).
{ transitivity (getr (ms_regs msA) 24); [exact (HPm 24 ltac:(unfold acallee_saved; lia)) |].
  rewrite RA24. exact (pab_i7_den0 EA 29 _ E29). }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 30 <= a < shadow_addr F + 43) ->
  ~ (F + 0xf8 <= a < F + 0xf8 + 96) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) memm a = aview rsegs (w_H W) memc a).
{ intros a Ha N1 N2 N3. rewrite (Hfrm a Ha N2 ltac:(lia)). exact (KA a Ha N1). }
(* ---- the entry state at 0x81040 ---- *)
pose proof (proj1 HJm) as HARm.
destruct ((al_frames _ _ LAWS) lyc Sc W memm mdm 4 pos HARm Hin4) as (_ & _ & HFpresm & _).
rewrite HFA in HFpresm. change (fs_frame_bytes 4) with 1024 in HFpresm.
assert (Vd0m : val_mem rsegs (mrestrict (w_H W) memm) (R + 0xd0) 8 (F + 0xf0)).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) memc memm _ 8 _); [|exact Vd0].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KM; lia. }
assert (V168m : val_mem rsegs (mrestrict (w_H W) memm) (R + 0x168) 8 pp).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) memc memm _ 8 _); [|exact V168].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KM; lia. }
assert (Vlenm : val_mem rsegs (mrestrict (w_H W) memm) (pp + 0x4000) 8 plen).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) memc memm _ 8 _); [|exact Vlen].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. unfold pab_i7_apart in Hsep, Hppsh. apply KM; lia. }
set (EB := Ereg regsm (pab_extra [F; pp])).
assert (F9 : ew EB 9 = Z_to_bv 64 R).
{ subst EB. rewrite (ew_Ereg_nat regsm _ 9 9%bv eq_refl). rewrite KRm by pab_i7_side. exact H9. }
assert (F33 : ew EB 33 = Z_to_bv 64 F) by reflexivity.
assert (F34 : ew EB 34 = Z_to_bv 64 pp) by reflexivity.
assert (F9u : bv_unsigned (ew EB 9) = R) by (rewrite F9; apply unsigned_lit_small; lia).
assert (F33u : bv_unsigned (ew EB 33) = F) by (rewrite F33; apply unsigned_lit_small; lia).
assert (HR0B : regs_ok EB sr_atoms regsm) by (subst EB; apply regs_ok_Ereg).
assert (HSB : st_ok rsegs EB pab_i7_ssB (restrict (w_H W) (mkst regsm (Z_to_bv 64 PAB_I7_RET1) memm (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); change (Ereg regsm (pab_extra [F; pp])) with EB.
  - exact HR0B.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rtmb_ro_region rsegs EB (w_H W) memm 9 R); [exact F9u | lia | lia |].
      constructor; [|constructor; [|constructor]].
      * apply (pab_chunk8 EB _ R 0xd0 (SOff 33 0xf0) (F + 0xf0)); [apply pab_i7_soff; exact F33 | lia | exact Vd0m].
      * apply (pab_chunk8 EB _ R 0x168 (SOff 34 0) pp);
          [rewrite (pab_i7_soff EB 34 pp 0 F34), Z.add_0_r; reflexivity | lia | exact V168m].
    + apply (rtmb_rw_region rsegs EB (w_H W) memm 33 F); [exact F33u | lia | lia | | constructor].
      intros o Ho. exact (proj1 (HFpresm (F + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val pab_i7_RB pab_i7_EH]. rewrite F9u, F33u. lia.
  - split; [exact I | split; exact I]. }
clearbody EB.
(* ---- 0x81040 .. 0x81054, to pod_write_ent's entry 0x83cc4 ---- *)
aj_run_to pab_tbl_ok HSB HJm PWE_ENT.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 33%nat pos 0);
    [reflexivity | rewrite F33u, HFA; lia | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HSx : st_ok _ EB _ (restrict _ ?m) |- _ => rename m into msB end.
lazymatch goal with HFx : frame_of EB _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into FRB end.
pab_i7_reg HSB (1%bv : bv 5) RB1. pab_i7_reg HSB (10%bv : bv 5) RB10. pab_i7_reg HSB (11%bv : bv 5) RB11.
assert (KRB : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clobB -> getr (ms_regs msB) r = getr regsm r).
{ exact (pab_i7_regs_kept EB _ msB regsm sr_atoms (w_H W) pab_i7_clobB HSB HR0B ltac:(vm_compute; reflexivity)). }
assert (KRBall : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clob -> getr (ms_regs msB) r = getr regs r).
{ intros r Hr0 Hn. rewrite (KRB r Hr0 (pab_i7_incl _ _ pab_i7_sub_B r Hn)). exact (KRm r Hr0 Hn). }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xf8) ->
  aview rsegs (w_H W) (ms_mem msB) a = aview rsegs (w_H W) memm a).
{ intros a Ha Hn. apply (pab_i7_keep_run EB (ss_mem pab_i7_ssB) (w_H W) memm (ms_mem msB)
    (fun x => F + 0xf0 <= x < F + 0xf8) FRB); [| exact Ha | exact Hn].
  intros x (r & Hr & Hb). cbv [pab_i7_ssB ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pab_i7_RB pab_i7_EH] in Hb;
    rewrite ?F9u, ?F33u in Hb; lia. }
pab_i7_regn HSB 1%nat RgEH.
(* e's 104 bytes: the two header words from the run, the 96 body bytes from the memset *)
assert (EBY : rtmb_bytes rsegs (w_H W) (ms_mem msB) (F + 0xf0) (Layout.ent_mem pab_e7)).
{ apply (proj2 (rtmb_bytes_aview rsegs _ _ _ _)). rewrite pab_e7_mem. intros j Hj.
  rewrite length_app, rtmb_length_repeat in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j 8) as [Hj8 | Hj8].
  - rewrite app_nth1 by (cbn [length]; lia).
    assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%nat) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    [ replace (F + 0xf0 + Z.of_nat 0) with (F + 240 + 0) by lia
    | replace (F + 0xf0 + Z.of_nat 1) with (F + 240 + 1) by lia
    | replace (F + 0xf0 + Z.of_nat 2) with (F + 240 + 2) by lia
    | replace (F + 0xf0 + Z.of_nat 3) with (F + 240 + 3) by lia
    | replace (F + 0xf0 + Z.of_nat 4) with (F + 244 + 0) by lia
    | replace (F + 0xf0 + Z.of_nat 5) with (F + 244 + 1) by lia
    | replace (F + 0xf0 + Z.of_nat 6) with (F + 244 + 2) by lia
    | replace (F + 0xf0 + Z.of_nat 7) with (F + 244 + 3) by lia ];
    pab_i7_lit_tac RgEH F33u; vm_compute; reflexivity.
  - rewrite app_nth2 by (cbn [length]; lia). cbn [length]. rewrite rtmb_nth_repeat by lia.
    rewrite KB by lia.
    replace (F + 0xf0 + Z.of_nat j) with (F + 0xf8 + (Z.of_nat j - 8)) by lia.
    rewrite (Heffm (Z.of_nat j - 8)) by lia. reflexivity. }
(* the frame's shadow at the call: e still in scope *)
assert (FSB : rt_fsh rsegs (w_H W) (ms_mem msB) F (rtmb_sh false false false true false false false)).
{ apply (rtmb_fsh_kept rsegs (w_H W) (ms_mem msA) (w_H W) (ms_mem msB) F _ FSA).
  intros i Hi. rewrite rtmb_sh_len in Hi. change (Z.of_nat 88) with 88 in Hi.
  unfold pab_i7_apart in HFsh. rewrite KB by lia. apply Hfrm; lia. }
assert (B2 : getr (ms_regs msB) 2 = w64 R) by (rewrite KRBall by pab_i7_side; exact H2).
assert (B3 : getr (ms_regs msB) 3 = w64 (as_gp B)) by (rewrite KRBall by pab_i7_side; exact H3).
assert (B4 : getr (ms_regs msB) 4 = w64 (as_tp B)) by (rewrite KRBall by pab_i7_side; exact H4).
assert (SPB : spZ (ms_regs msB) = R) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
assert (B1 : getr (ms_regs msB) 1 = w64 PWE_RA_SHAPE7) by (rewrite RB1; reflexivity).
assert (B10 : getr (ms_regs msB) 10 = w64 pp) by (rewrite RB10, (pab_i7_soff EB 34 pp 0 F34), Z.add_0_r; reflexivity).
assert (B11 : getr (ms_regs msB) 11 = w64 (F + 0xf0)) by (rewrite RB11, (pab_i7_soff EB 33 F 240 F33); reflexivity).
assert (VlenB : val_mem rsegs (mrestrict (w_H W) (ms_mem msB)) (pp + Layout.OFF_LEN) 8 plen).
{ unfold Layout.OFF_LEN. apply (val_mem_kept rsegs (w_H W) (w_H W) memm (ms_mem msB) _ 8 _); [|exact Vlenm].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. unfold pab_i7_apart in Hsep. apply KB; lia. }
pose proof (rtmb_B_ra_e rsegs (w_H W) (ms_mem msB) F false false false false false false 0 104 FSB FB8
  ltac:(lia) ltac:(lia)) as RAq.
unfold RTMB_E in RAq. rewrite Z.add_0_r in RAq.
pose proof (pab_i7_hull (w_H W) (ms_mem msB) F _ 0xf0 104 FSB HF32 ltac:(lia) ltac:(lia)
  ltac:(rewrite rtmb_sh_len; change (Z.of_nat 88) with 88; lia)) as HULLq.
rewrite (st_ok_restrict_mkst rsegs (w_H W) EB _ msB HSB eq_refl) at 1.
(* ---- the call: pod_write_ent(pp, F + 0xf0), ra = 0x81058 ---- *)
eapply SRr_bind.
{ apply (rtsb_pwe_at B MT STK sp0 FP ly S W0 mem0 md0 own k (ms_regs msB) lyc Sc W (ms_mem msB) _ pp plen
    PWE_RA_SHAPE7 (R - sp0) pab_e7 (pab_i7_pwR W (ms_mem msB) pp plen (F + 0xf0))).
  - exact B1.
  - rewrite SPB. lia.
  - pose proof (proj1 HJm) as HARB.
    destruct (pwe_pp_of_block rsegs B lyc Sc W (ms_mem msB) _ pp HARB Hpp) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    destruct (rtsb_pwe_site F 0xf0 (F + 0xf0) pp R HF32 HFapp eq_refl ltac:(lia) eq_refl
      ltac:(unfold Layout.ENT_SIZE; lia) ltac:(unfold pab_i7_apart in Hsep; exact Hsep)
      ltac:(left; rewrite HTP; lia)) as (S1 & S2 & S3 & S4 & S5).
    apply (PWE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msB) _ k (ms_regs msB) pp (F + 0xf0) plen pab_e7).
    + unfold pw_pre. split; [exact HJm|].
      split; [rewrite B1; apply ret_ok_even; vm_compute; reflexivity|].
      split; [unfold raZ; rewrite B1; unfold w64, PWE_RA_SHAPE7; rewrite unsigned_lit_small by lia; lia|].
      split; [exact B3|]. split; [exact B4|].
      rewrite SPB. split; [exact HR16|]. split; [rewrite HTP; lia|]. split; [lia|]. exact Hev.
    + exact B10.
    + exact B11.
    + exact Q1.
    + exact Q2.
    + exact Q3.
    + exact Q4.
    + exact Q5.
    + exact Q6.
    + intros x Hx. eapply pwe_awr_fresh with (len := plen) (e := pab_e7);
        [exact Hpp | exact Hpp0 | exact Hp0 | rewrite pab_e7_len; unfold Layout.POD_BUF_MAX; lia | exact Hx].
    + rewrite SPB. left. unfold Layout.PP_SIZE. rewrite HTP. lia.
    + exact VlenB.
    + exact Hp0.
    + exact Hp8.
    + rewrite pab_e7_len. unfold Layout.POD_BUF_MAX. lia.
    + exact S1.
    + exact S2.
    + exact S3.
    + reflexivity.
    + unfold pab_e7, Layout.ENT_SIZE. cbn [Model.e_size]. lia.
    + unfold pab_e7, Model.POD_INT. cbn [Model.e_type]. lia.
    + exact EBY.
    + exact RAq.
    + exact HULLq.
    + exact S4.
    + rewrite SPB. exact S5. }
cbv beta. intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HPR).
unfold pab_i7_pwR in HPR. destruct HPR as (P1 & P2 & _ & _ & _).
rewrite pab_e7_len in P2. unfold Layout.OFF_LEN in P2.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (pp + plen <= a < pp + plen + 16) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (R - T_pwe_STK <= a < R) -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) (ms_mem msB) a).
{ intros a Ha N1 N2 N3. apply Hm3; [exact Ha|]. unfold pwe_E. rewrite pab_e7_len. unfold Layout.OFF_LEN.
  intros [[X|X]|X]; [apply N1 | apply N2 | apply N3]; lia. }
assert (KR3 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clob -> getr regs3 r = getr regs r).
{ intros r Hr0 Hn. rewrite (Hr3 r Hr0 (pab_i7_incl _ _ pab_i7_sub_cs r Hn)). exact (KRBall r Hr0 Hn). }
(* ---- the entry state at 0x81058 ---- *)
assert (Hin4' : In (4, pos) (frames S3)) by (rewrite Hf3; exact Hin4).
assert (HFA3 : frame_addr ly3 4 pos = F) by (rewrite <- HFA; eapply (pab_i7_faddr B); [exact HJm | exact HJ3]).
pose proof (proj1 HJ3) as HAR3.
destruct ((al_frames _ _ LAWS) ly3 S3 W3 mem3 md3 4 pos HAR3 Hin4') as (_ & _ & _ & HFSpres3).
rewrite HFA3 in HFSpres3. change (fs_frame_bytes 4) with 1024 in HFSpres3. change (1024 / 8) with 128 in HFSpres3.
assert (G19 : getr regs3 19 = w64 (shadow_addr F)) by (rewrite KR3 by pab_i7_side; exact H19).
set (EC := Ereg regs3 (pab_extra [])).
assert (G19e : ew EC 19 = Z_to_bv 64 (shadow_addr F)) by (subst EC; rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact G19).
assert (G19u : bv_unsigned (ew EC 19) = shadow_addr F) by (rewrite G19e; apply unsigned_lit_small; lia).
assert (E18c : ew EC 18 = getr regs3 18) by (subst EC; apply ew_Ereg_nat; reflexivity).
assert (E22c : ew EC 22 = getr regs3 22) by (subst EC; apply ew_Ereg_nat; reflexivity).
assert (E24c : ew EC 24 = getr regs3 24) by (subst EC; apply ew_Ereg_nat; reflexivity).
assert (HR0C : regs_ok EC sr_atoms regs3) by (subst EC; apply regs_ok_Ereg).
assert (HSC : st_ok rsegs EC pab_i7_ssC (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 PWE_RA_SHAPE7) mem3 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); change (Ereg regs3 (pab_extra [])) with EC.
  - exact HR0C.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_rw_region rsegs EC (w_H W3) mem3 19 (shadow_addr F)); [exact G19u | lia | lia | | constructor].
    intros o Ho. exact (proj1 (HFSpres3 o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
clearbody EC.
change (w64 PWE_RA_SHAPE7) with (Z_to_bv 64 PWE_RA_SHAPE7).
(* ---- 0x81058 .. 0x810a0, to 0x8257c ---- *)
aj_run_to pab_tbl_ok HSC HJ3 PAB_LATCH7.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  apply (rtsb_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat pos);
    [reflexivity | rewrite G19u, HFA3; reflexivity | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HSx : st_ok _ EC _ (restrict _ ?m) |- _ => rename m into msC end.
lazymatch goal with HFx : frame_of EC _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into FRC end.
pab_i7_reg HSC (5%bv : bv 5) RC5. pab_i7_reg HSC (13%bv : bv 5) RC13.
pab_i7_reg HSC (24%bv : bv 5) RC24. pab_i7_reg HSC (29%bv : bv 5) RC29.
assert (KRC : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pab_i7_clobC -> getr (ms_regs msC) r = getr regs3 r).
{ exact (pab_i7_regs_kept EC _ msC regs3 sr_atoms (w_H W3) pab_i7_clobC HSC HR0C ltac:(vm_compute; reflexivity)). }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 30 <= a < shadow_addr F + 43) ->
  aview rsegs (w_H W3) (ms_mem msC) a = aview rsegs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (pab_i7_keep_run EC (ss_mem pab_i7_ssC) (w_H W3) mem3 (ms_mem msC)
    (fun x => shadow_addr F + 30 <= x < shadow_addr F + 43) FRC); [| exact Ha | exact Hn].
  intros x (r & Hr & Hb). cbv [pab_i7_ssC ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val pab_i7_SH] in Hb;
    rewrite ?G19u in Hb; lia. }
pab_i7_regn HSC 0%nat RgSC.
assert (SHC : forall i, 30 <= i < 43 -> aview rsegs (w_H W3) (ms_mem msC) (shadow_addr F + i) = Some 248).
{ intros i Hi. replace (shadow_addr F + i) with (shadow_addr F + i + 0) by ring.
  assert (Hc : i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/
    i = 40 \/ i = 41 \/ i = 42) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
  pab_i7_lit_tac RgSC G19u; vm_compute; reflexivity. }
(* every byte outside the block's write set as at its start *)
assert (KFIN : forall a, 0 <= a < 2 ^ 64 -> ~ pab_i7_Wr R F pp plen a ->
  aview rsegs (w_H W3) (ms_mem msC) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. unfold pab_i7_Wr in Hn.
  rewrite (KC a Ha ltac:(intro X; apply Hn; right; left; exact X)).
  rewrite (KP a Ha ltac:(intro X; apply Hn; right; right; left; exact X)
    ltac:(intro X; apply Hn; right; right; right; left; exact X)
    ltac:(intro X; apply Hn; right; right; right; right; exact X)).
  rewrite (KB a Ha ltac:(intro X; apply Hn; left; clear Hn; lia)).
  apply KM; [exact Ha | intro X; apply Hn; right; left; exact X | intro X; apply Hn; left; clear Hn; lia |].
  intro X; apply Hn; right; right; right; right; clear Hn; rewrite HTP; rewrite HES in X; lia. }
(* ---- the leaf ---- *)
apply SRr_ret. red.
exists ly3, S3, (ms_regs msC), (ms_mem msC). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W3) EC _ msC HSC eq_refl) at 1; reflexivity|].
split; [exact HJ3|].
split.
{ intros r Hr0 Hn. rewrite (KRC r Hr0 (pab_i7_incl _ _ pab_i7_sub_C r Hn)). exact (KR3 r Hr0 Hn). }
split; [exact Hf3|].
split; [exact Hp3|].
split.
{ eapply same_io_trans; [eapply same_io_trans; [eapply same_io_trans; [eapply same_io_trans;
    [apply same_io_wvb | apply same_io_materialized; exact Hsmm] | apply same_io_wvb] | exact Hio3] | apply same_io_wvb]. }
split; [exact Hmo3|].
split; [exact KFIN|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
- rewrite RC5, (pab_i7_den0 EC 18 _ E18c).
  rewrite Hr3 by pab_i7_side. rewrite KRB by pab_i7_side.
  exact M18.
- rewrite RC29, (pab_i7_den0 EC 24 _ E24c).
  rewrite Hr3 by pab_i7_side. rewrite KRB by pab_i7_side.
  exact M24.
- rewrite RC24. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity.
- rewrite RC13, (pab_i7_den0 EC 22 _ E22c). apply KR3; pab_i7_side.
- intros i Hi. replace (Z.of_nat (length rsb_P0)) with 88 in Hi by reflexivity.
  destruct (Z_lt_le_dec i 30) as [L|L]; [|destruct (Z_lt_le_dec i 43) as [U|U]].
  + rewrite KFIN; [exact (Hfsh0 i ltac:(replace (Z.of_nat (length rsb_P0)) with 88 by reflexivity; lia)) | lia |].
    unfold pab_i7_Wr, pab_i7_apart in *. rewrite HTP. lia.
  + rewrite (SHC i ltac:(lia)). f_equal. symmetry.
    apply (rtmb_nth_range rsb_P0 30 13 248 ltac:(vm_compute; reflexivity)). lia.
  + rewrite KFIN; [exact (Hfsh0 i ltac:(replace (Z.of_nat (length rsb_P0)) with 88 by reflexivity; lia)) | lia |].
    unfold pab_i7_Wr, pab_i7_apart in *. rewrite HTP. lia.
- rewrite <- pab_e7_enc.
  apply (rtmb_bytes_kept rsegs (w_H W3) mem3 (w_H W3) (ms_mem msC) (pp + plen) (Model.enc_pod pab_e7) P1).
  intros x Hx. rewrite pab_e7_len' in Hx. unfold pab_i7_apart in Hppsh. apply KC; lia.
- apply (val_mem_kept rsegs (w_H W3) (w_H W3) mem3 (ms_mem msC) _ 8 _); [|exact P2].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. unfold pab_i7_apart in Hppsh. apply KC; lia.
Qed.

End d.
End b.

(* ================================ the shape-7 Int pod piece: SEL7 -> LATCH7 ================================ *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the memset contract (__asan_memset 0x51d54), which the block calls on e's body *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51d54.
(* pod_write_ent's contract (lib/AU/PweSpec.v, its entry 0x83cc4), which the block calls on pp and e *)
Hypothesis PWE : pod_write_ent_specX rsegs B MT 0x83cc4.

Lemma pab_piece_int7 : rsb_piece_W4_int7_stmt rsegs B MT.
Proof using MTL LAWS AMEMSET PWE.
unfold rsb_piece_W4_int7_stmt. intros cx POST rest i Hst HL7.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pab_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pab_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3 & FB4).
pose proof (pab_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (HJ0 & Hev & G2 & G3 & G4 & _ & _ & _ & _ & Hown & HF & _).
cbn [hi_cid rate_himg_B] in Hown, HF.
assert (Hrq : req_size Layout.PP_SIZE = 19744) by reflexivity.
assert (Hin4 : In (4, x_pos cx) (frames (x_Sc cx))).
{ pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs0 & _). rewrite Hfrs0. apply in_or_app. left. exact Hown. }
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 (x_pos cx) (proj1 HJ0) Ppin Hin4) as Hdisj.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite <- HF, Hrq in Hdisj.
change (fs_frame_bytes 4) with 1024 in Hdisj.
pose proof (rtsb_fbounds (q_F (x_e cx)) FB4 FB3) as (_ & _ & Hsh0 & HshC & _ & _).
unfold rsb_from_SEL7. intros ly2 S2 W2 regs2 mem2 md2 np ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hqlen & Hps & Hsh & Hnp & Hpsl & Hnp3).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
assert (Ppin2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
assert (FA2 : frame_addr ly2 4 (x_pos cx) = q_F (x_e cx)).
{ rewrite HF. eapply (pab_i7_faddr B); [exact HJ0 | exact HJ]. }
destruct (pab_img_bounds 7 ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold rsb_at_cx in Hat.
pab_take Hat (LReg 9) (q_R (x_e cx)) A9. pab_take Hat (LReg 19) (shadow_addr (q_F (x_e cx))) A19.
pab_take Hat (LReg 5) (Z.of_nat (length ps)) A5. pab_take Hat (LReg 29) (Z.of_nat (length r)) A29.
pab_take Hat (LReg 22) (rsb_seen ps) A22.
pab_take Hat (LCell XR 0xb8) (q_F (x_e cx) + 0xf8) Ab8. pab_take Hat (LCell XR 0xd0) (q_F (x_e cx) + 0xf0) Ad0.
pab_take Hat (LCell XR 0x168) (q_pp (x_e cx)) A168.
assert (PB2' : q_pp (x_e cx) + 19744 <= alloc_ceiling) by exact PB2.
rewrite Z.mod_small in Ab8 by lia. rewrite Z.mod_small in Ad0 by lia. rewrite Z.mod_small in A168 by lia.
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))) by (exact (eq_trans (Hr234 2 ltac:(lia)) RB6)).
assert (A3 : getr regs2 3 = w64 (as_gp B)) by (exact (eq_trans (Hr234 3 ltac:(lia)) G3)).
assert (A4 : getr regs2 4 = w64 (as_tp B)) by (exact (eq_trans (Hr234 4 ltac:(lia)) G4)).
assert (Hplen : rsb_plen 7 ps = Z.of_nat (length (pc_buf (PbCut 7 ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rsb_plen 7 ps)).
{ rewrite Hplen. unfold rsb_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut 7 ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rtmb_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (pab_int7 B MT MTL LAWS AMEMSET PWE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (q_F (x_e cx))
    (q_pp (x_e cx)) (rsb_plen 7 ps) (x_pos cx)
    HJ Hev A2 A3 A4 A9 A19 RB1 RB2 RB3 RB5 RB7 Hown FA2 FB4 FB3 Ppin2 Ppout Hdisj Ab8 Ad0 A168 Alen _ _ _ Hfsh);
  rewrite ?Hplen; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R5 & R29 & R24 & R13 & Rfsh & Rpp & Rlen).
set (R := q_R (x_e cx)) in *. set (pp := q_pp (x_e cx)) in *. set (F := q_F (x_e cx)) in *.
set (plen := rsb_plen 7 ps) in *.
assert (SP : spZ (x_regs cx) = R).
{ unfold spZ. rewrite RB6. unfold w64. apply unsigned_lit_small. lia. }
assert (HTP : T_pwe_STK = 4144) by reflexivity.
assert (Hpl : 0 <= plen <= 5424) by (rewrite Hplen; lia).
(* the bytes of R the block keeps: every cell of the cut lists lies at R + 0 .. R + 0x180 *)
assert (KR : forall o j, 0 <= o <= 0x178 -> 0 <= j < 8 ->
  aview rsegs (w_H W3) mem3 (R + o + j) = aview rsegs (w_H W2) mem2 (R + o + j)).
{ intros o j Ho Hj. apply Hmem; [unfold T_SEG_STK, ASTACK in *; lia|].
  unfold pab_i7_Wr. rewrite HTP. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcore3 : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pab_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pab_regs234 Hkeep.
  - intros a Ha. rewrite SP. unfold pab_i7_Wr in Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    + right. apply pab_E1_F. fold F. lia.
    + right. apply pab_E1_shF. fold F. lia.
    + right. apply pab_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + right. apply pab_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + left. rewrite HTP in Ha. unfold T_SEG_STK, ASTACK. lia. }
assert (Hfsh3 : rsb_fsh_at rsegs cx W3 mem3 rsb_P0) by exact Rfsh.
(* the locations the block keeps: every register of rsb_Rc0, s9 and s10 (none is in pab_i7_clob), and every cell
   of R *)
assert (Hat3 : rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rsb_Rc0 rsegs cx ++ [(LReg 25, 1)] ++ rsb_Kc rsegs cx 7 np ++ rsb_Hc rsegs cx ++ [(LReg 26, rsb_cur rsegs cx rest r)])).
{ eapply pab_at_move; [pab_list; pab_from Hat|].
  cbn [rsb_Rc0 rsb_Kc rsb_Hc app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pab_kept_loc rt_xv].
  all: try (apply Hkeep; pab_i7_side).
  all: let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R; apply KR; lia. }
assert (Hpp3 : rsb_pp_at rsegs cx W3 mem3 (pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None))).
{ unfold rsb_pp_at. rewrite pab_img7. fold pp.
  unfold rsb_pp_at, pc_image in Hpp. fold pp in Hpp.
  assert (Lx : length (prop_bytes 7 (0, PInt 0)) = 16%nat) by reflexivity.
  eapply (pab_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite Lx, Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - rewrite <- Hplen. fold plen. exact Rpp.
  - rewrite Lx, Nat2Z.inj_add, <- Hplen. fold plen. unfold Layout.OFF_LEN.
    replace (plen + Z.of_nat 16) with (plen + 16) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite Lx, <- Hplen in Hx. fold plen in Hx.
    unfold Layout.OFF_LEN in Hl. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    destruct ((al_blocks _ _ LAWS) _ _ _ _ _ pp Layout.PP_SIZE (proj1 HJ0) Ppin) as (_ & _ & _ & Happ & _).
    rewrite Hrq in Happ.
    pose proof (pab_i7_sh_apart F pp 19744 FB1 FB2 Happ ltac:(lia)) as X. unfold pab_i7_apart in X.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|].
    unfold pab_i7_Wr. rewrite HTP. unfold T_SEG_STK, ASTACK, Layout.PP_SIZE in *. lia. }
change (mkCfg (mkst regs3 (w64 PAB_LATCH7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RSB_LATCH7 regs3 mem3 md3).
apply (HL7 ly3 S3 W3 regs3 mem3 md3 7 np (ps ++ [(0, PInt 0)]) r ltac:(rewrite length_app, Hlen; cbn; lia)).
split.
- split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply pab_wf7; [exact Hwf | lia]|]. split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn; lia|]. split; [exact Hnp3|].
  rewrite length_app, Nat.add_1_r, pab_loop7, <- Hps, <- Hr. reflexivity.
- (* s8 = -8, t0 = i, t4 = |r| and a3 = seen from the block's relation; every other location kept *)
  unfold rsb_at_cx. rewrite pab_seen7. pab_list; first [pab_from Hat3 | idtac].
  + cbn [rt_at]. exact R24.
  + cbn [rt_at]. refine (eq_trans R5 _). refine (eq_trans A5 _). rewrite length_app. cbn [length]. f_equal. lia.
  + cbn [rt_at]. exact (eq_trans R29 A29).
  + cbn [rt_at]. exact (eq_trans R13 A22).
Qed.
End p.

Print Assumptions pab_piece_int7.
