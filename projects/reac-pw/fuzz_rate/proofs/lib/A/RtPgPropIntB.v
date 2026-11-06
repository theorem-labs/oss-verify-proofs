(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the shape-7 Int pod block SEL7
   0x80e6c -> LATCH7 0x82530 of LLVMFuzzerTestOneInput, as a block lemma over lib/A/RtPgPropKit.v, and the piece
   rs_piece_W4_int7_stmt of lib/A/RtPgSeg.v. Proves no function (kind: segment lemma).

   THE BLOCK (pod.h:177-197, pod_put32(pp, 4) twice, pod_put(pp, zero body, 4), the pad of pod.h:187)
     0x80e6c .. 0x80fb4   three 4-byte puts at pp + len (len = plen, plen + 4, plen + 8): the capacity test
                          `bltu len - 0x3ffd, s10` (s10 = -0x4001; the second and third read -0x3ffd from R+0x130;
                          never taken: plen + 16 <= 5440 < 0x4000), the two shadow checks of pp + len and pp + len + 3
                          (EQ-J; the out-of-line slow blocks 0x82550 .. 0x825a0 are dead, the shadow of pp's block is
                          0 there), the four byte stores, the shadow check of the len cell pp + 0x4000 (through s6)
                          and len += 4 (through s7).
     0x80fb8 .. 0x80fec   the len cell's check, `mv s10,s8` (s10 = what is left of the input), s8 = (-len) & 7 = 4,
                          `bltu 0x4000, s8 + len` (not taken), `jal 0x51cfc` (__asan_memset(pp + len, 0, 4),
                          ra = 0x80ff0).
     0x80ff0 .. 0x81014   the len cell's check, len += s8, a6 = i (R+0xf8), s8 = s10, s10 = -0x4001 (R+0x118),
                          `j 0x82530`.
   ROUTE. The engine runs 0x80e6c to the call at 0x51cfc (outside pa_tbl), with pp + plen named as its own atom (34,
   the alias fact pp + plen = atom 34 makes `add a0,s11,a0` give SOff 34 c), s8 named as atom 35 (it is only moved), a
   shadow entry over [pp + plen, pp + plen + 32) and over pp's whole block (every check is then decided with a zero
   shadow byte), and the three capacity tests as assumed conditions of the entry facts. The call is __asan_memset's
   contract (Section hypothesis AMEMSET) through lib/A/RtPgSteps.v rts_intrin_at. After the call a fresh entry state
   at 0x80ff0 carries what the call kept (the len cell, R+0xf8, R+0x118, s8 = 4 and s10 by aregs_preserved) and the
   engine runs to 0x82530. *)
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
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgPropKit RtPgPropLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgSteps.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

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
(* the registers the block may change: ra, t0-t2, a0-a7, s8, s10, t3-t6 (the memset call's caller-saved set, and s8 /
   s10, which the block uses around the pad and restores to their values at the block's start) *)
Definition pa_clob_call : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 28; 29; 30; 31]%bv.
(* the 16 bytes the block writes at pp + plen: put32 4 (size), put32 4 (type), 4 zero body bytes, 4 pad bytes *)
Definition pa_int7_bytes : list Z := [4; 0; 0; 0; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition PA_I_MEMSET : Z := 0x51cfc.
Definition PA_I_RET : Z := 0x80ff0.

(* ---- the two engine states ---- *)
(* s6 = (pp + 0x4000 >> 3) + K, the len cell's shadow address *)
Definition pa_i_s6 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 32 0).
(* 0x80e6c: atoms 9 R, 27 pp, 32 K, 33 plen, 34 pp + plen, 35 what is left of the input (s8) *)
Definition pa_i_SHA : list shent := [mkSHE 27 0 19744; mkSHE 34 0 32].
Definition pa_i_factsA : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 4096 140737479946976 4);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 5424 3); (34%nat, mkAF 4096 140737479952400 3) ]
  [ mkAC BC_GEU (SOff 33 (-16381)) (SLit (-16385)); mkAC BC_GEU (SOff 33 (-16377)) (SLit (-16385));
    mkAC BC_GEU (SOff 33 (-16373)) (SLit (-16385)) ]
  [ (SAlu ALU_ADD (SOff 27 0) (SOff 33 0), SOff 34 0) ].
Definition pa_i_regsA : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (22%bv : bv 5) pa_i_s6)
    (23%bv : bv 5) (SOff 27 16384)) (18%bv : bv 5) (SOff 32 0)) (10%bv : bv 5) (SOff 33 0))
    (12%bv : bv 5) (SOff 33 (-16381))) (26%bv : bv 5) (SLit (-16385))) (24%bv : bv 5) (SOff 35 0).
Definition pa_i_slotsA : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0
  [ YP09.mkChunk 0x130 (CVal 8 (SLit (-16381))) ].
Definition pa_i_lenA : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0)) ].
Definition pa_i_body : YP09.region := YP09.mkRegion (Some 34%nat) 0 16 0 16 [].
Definition pa_i_ssA : sstate := mkSS PA_SEL7 pa_i_regsA [pa_i_slotsA; pa_i_lenA; pa_i_body] None pa_i_factsA.
(* 0x80ff0: atoms 9 R, 27 pp, 32 K, 33 plen, 35 i, 36 what is left of the input (in s10 here) *)
Definition pa_i_SHB : list shent := [mkSHE 27 0 19744].
Definition pa_i_factsB : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 4096 140737479946976 4);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 5424 3); (35%nat, mkAF 0 2 0) ] [] [].
Definition pa_i_regsB : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (22%bv : bv 5) pa_i_s6)
    (23%bv : bv 5) (SOff 27 16384)) (18%bv : bv 5) (SOff 32 0)) (24%bv : bv 5) (SLit 4)) (26%bv : bv 5) (SOff 36 0).
Definition pa_i_slotsB : YP09.region := YP09.mkRegion (Some 9%nat) 0xf8 0x120 0 0
  [ YP09.mkChunk 0xf8 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x118 (CVal 8 (SLit (-16385))) ].
Definition pa_i_lenB : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 33 12)) ].
Definition pa_i_ssB : sstate := mkSS PA_I_RET pa_i_regsB [pa_i_slotsB; pa_i_lenB] None pa_i_factsB.

(* ---- arithmetic ---- *)
Lemma pa_i_bytes_range : forall j, 0 <= nth j pa_int7_bytes 0 < 256.
Proof.
intros j. destruct (nth_in_or_default j pa_int7_bytes 0) as [Hin | ->]; [|lia].
generalize dependent (nth j pa_int7_bytes 0). intros v Hin. cbv [pa_int7_bytes In] in Hin. repeat (destruct Hin as [<- | Hin]; [lia|]). destruct Hin.
Qed.
Lemma pa_i_mod8 : forall a b, a mod 16 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof.
intros a b Ha Hb. rewrite (Z.div_mod a 16) by lia. rewrite (Z.div_mod b 8) by lia. rewrite Ha, Hb, !Z.add_0_r.
replace (16 * (a / 16) + 8 * (b / 8)) with ((2 * (a / 16) + b / 8) * 8) by ring. apply Z.mod_mul. lia.
Qed.
Lemma pa_i_mod16_sub : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. rewrite (Z.div_mod a 16) by lia. rewrite (Z.div_mod b 16) by lia. rewrite Ha, Hb, !Z.add_0_r.
replace (16 * (a / 16) - 16 * (b / 16)) with ((a / 16 - b / 16) * 16) by ring. apply Z.mod_mul. lia.
Qed.
Lemma pa_i_zneg : forall z, - M64 <= z < 0 -> zcanon z = z + M64.
Proof.
intros z Hz. unfold zcanon. rewrite <- (Z_mod_plus_full z 1 M64). rewrite Z.mul_1_l. apply Z.mod_small. lia.
Qed.

(* ---- values of symbolic terms ---- *)
Lemma pa_i_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma pa_i_s6_denot : forall E pp, ew E 27 = Z_to_bv 64 pp -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= pp -> pp + 16384 < 2 ^ 64 -> sv_denot E pa_i_s6 = w64 (shadow_addr (pp + 0x4000)).
Proof.
intros E pp H27 H32 H0 H1.
rewrite (match_x_denot (SOff 32 0) E pa_i_s6 (SOff 27 16384) ltac:(vm_compute; reflexivity)).
unfold cell_x, w64, shadow_addr. f_equal.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia). rewrite (U_atom_off E 27 pp 16384 H27) by lia.
reflexivity.
Qed.

(* ---- registers ---- *)
Definition pa_i_nz : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pa_i_bv5_cases : forall r : bv 5, bv_unsigned r <> 0 ->
bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/
bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/
bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/
bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/
bv_unsigned r = 31.
Proof. intros r Hr. pose proof (u5_range r) as Hb. lia. Qed.
Lemma pa_i_in_nz : forall r : bv 5, bv_unsigned r <> 0 -> In r pa_i_nz.
Proof.
intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r).
pose proof (pa_i_bv5_cases r Hr) as H.
repeat (destruct H as [H|H]; [rewrite H; cbv [pa_i_nz In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
rewrite H. cbv [pa_i_nz In]. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
(* a register outside pa_clob_call is callee-saved for the memset call *)
Lemma pa_i_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pa_clob_call -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr Hn. unfold acallee_saved.
pose proof (pa_i_bv5_cases r Hr) as H.
repeat (destruct H as [H|H];
  [ first [ lia
          | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [pa_clob_call In];
            repeat (first [left; apply bv_eq; reflexivity | right]) ] |]).
first [ lia
      | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [pa_clob_call In];
        repeat (first [left; apply bv_eq; reflexivity | right]) ].
Qed.

Lemma pa_i_notin : forall r : bv 5, existsb (fun c => bv_eqb c r) pa_clob_call = false -> ~ In r pa_clob_call.
Proof.
intros r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) pa_clob_call = true).
{ apply existsb_exists. exists r. split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]. }
rewrite H in Ht. discriminate Ht.
Qed.
(* across the memset call: a register outside pa_clob_call is callee-saved, so the call keeps it *)
Lemma pa_i_pres : forall (r0 r1 : bvmap 5 word) (r : bv 5), aregs_preserved r0 r1 ->
bv_unsigned r <> 0 -> ~ In r pa_clob_call -> getr r1 r = getr r0 r.
Proof.
intros r0 r1 r HP Hr Hn. pose proof (HP (bv_unsigned r) (pa_i_cs r Hr Hn)) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Ltac pa_i_keep_reg KR :=
apply KR; [let Hz := fresh "Hz" in intro Hz; vm_compute in Hz; discriminate Hz | apply pa_i_notin; vm_compute; reflexivity].

Section k. Context {fx : YK11.FPState}.
(* a register whose symbolic value at the end of a run is the one it had at the entry kept its value (the entry
   values may be overrides, not only atoms) *)
Lemma pa_i_regs_kept : forall E ss ms regs0 sr0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) pa_i_nz = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 sr0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (pa_i_in_nz r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. apply HR.
Qed.
(* the value of one chunk of a region [cgif lib/A/AC8j.v field_of_region] *)
Lemma pa_i_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
End k.

(* the symbolic value of register r at the end of a run *)
Ltac pa_i_reg HS r Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hn : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg sg Hh E ss ms r HS)
end.
(* region i of the state at the end of a run [lib/A/RtPgSteps.v rts_region_nth] *)
Ltac pa_i_regn HS i Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
assert (Hn : region_ok sg E (mrestrict Hh (ms_mem ms)) rg) by (apply (rts_region_nth E ss ms i rg Hh HS); vm_compute; reflexivity)
end end.
(* the write windows of a run's entry state lie in the zone the goal names *)
Ltac pa_i_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => rewrite Hu in Hb end; lia | ]); destruct Hr.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51cfc.
Local Abbreviation pa_post := (rts_post B MT).

(* what the block computes, at LATCH7: a6 = i, s8 and s10 restored (nr = what is left of the input, -0x4001), the 16
   bytes at pp + plen, len = plen + 16 *)
Lemma pa_int7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp i plen nr : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 27 = w64 pp -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 10 = w64 plen -> getr regs 12 = w64 (plen - 0x3ffd) ->
getr regs 26 = w64 (-0x4001) -> getr regs 24 = w64 nr ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 i ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (2 ^ 64 - 0x4001) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen -> plen + 16 <= 5440 -> plen mod 8 = 0 -> 0 <= i <= 2 ->
SRr rsegs W (cfg_at rsegs PA_SEL7 regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc PA_LATCH7 pa_clob_call
 (fun a => pp + plen <= a < pp + plen + 16 \/ pp + 0x4000 <= a < pp + 0x4008 \/ R - ESTACK <= a < R)
 (fun W2 regs2 mem2 => getr regs2 16 = w64 i /\ getr regs2 24 = w64 nr /\ getr regs2 26 = w64 (-0x4001) /\
   garr8 rsegs (mrestrict (w_H W2) mem2) (pp + plen) pa_int7_bytes /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (plen + 16))).
Proof using MTL LAWS AMEMSET.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp i plen nr
HJ H2 H3 H4 H9 H27 H23 H22 H18 H10 H12 H26 H24 HRlo HRhi HR16 Hpp Hpp0 Vi Ve118 Ve130 Vlen Hp0 Hp16 Hp8 Hi.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct ((al_blocks _ _ LAWS) lyc Sc W memc mdc pp Layout.PP_SIZE HAR Hpp) as (Hpp16 & Hpp4096 & Hppceil & Hppapp & Hpppres & _).
assert (Hrq : req_size Layout.PP_SIZE = 19744) by reflexivity.
rewrite Hrq in Hppceil, Hppapp, Hpppres.
unfold T_SEG_STK, ASTACK in HRlo.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hppl : pp + plen + 16 <= pp + 5440) by lia.
assert (HppR : pp + 19744 < R - 4096) by lia.
(* ---- the entry state at 0x80e6c ---- *)
set (EA := Ereg regs (pa_extra [plen; pp + plen; nr])).
assert (E9 : ew EA 9 = Z_to_bv 64 R) by (subst EA; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E27 : ew EA 27 = Z_to_bv 64 pp) by (subst EA; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew EA 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew EA 33 = Z_to_bv 64 plen) by reflexivity.
assert (E34 : ew EA 34 = Z_to_bv 64 (pp + plen)) by reflexivity.
assert (E35 : ew EA 35 = Z_to_bv 64 nr) by reflexivity.
assert (E9u : bv_unsigned (ew EA 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E27u : bv_unsigned (ew EA 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew EA 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E33u : bv_unsigned (ew EA 33) = plen) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew EA 34) = pp + plen) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok EA pa_i_regsA regs).
{ unfold pa_i_regsA. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
  [apply regs_ok_pin; [apply regs_ok_pin;
  [subst EA; apply regs_ok_Ereg | | ] | | ] | | ] | | ] | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  - rewrite H22. symmetry. apply (pa_i_s6_denot EA pp E27 E32); lia.
  - rewrite H23, (pa_i_soff EA 27 pp 16384 E27). reflexivity.
  - rewrite H18, (pa_i_soff EA 32 SHADOW_OFF 0 E32), Z.add_0_r. reflexivity.
  - rewrite H10, (pa_i_soff EA 33 plen 0 E33), Z.add_0_r. reflexivity.
  - rewrite H12, (pa_i_soff EA 33 plen (-16381) E33). unfold w64. f_equal; lia.
  - rewrite H26. reflexivity.
  - rewrite H24, (pa_i_soff EA 35 nr 0 E35), Z.add_0_r. reflexivity. }
assert (HS : st_ok rsegs EA pa_i_ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_SEL7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs);
  change (Ereg regs (pa_extra [plen; pp + plen; nr])) with EA.
  - exact HR0.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (rtm_ro_region rsegs EA (w_H W) memc 9 R); [exact E9u | lia | lia |].
      constructor; [|constructor].
      eapply (pa_chunk8 EA _ R 0x130 (SLit (-16381)) (2 ^ 64 - 0x3ffd)); [cbn [sv_denot]; apply Z_to_bv64_eq_mod; reflexivity | lia | exact Ve130].
    + apply (rtm_rw_region rsegs EA (w_H W) memc 27 pp); [exact E27u | lia | lia | |].
      * intros o Ho. apply Hpppres. lia.
      * constructor; [|constructor].
        eapply (pa_chunk8 EA _ pp 0x4000 (SOff 33 0) plen); [rewrite (pa_i_soff EA 33 plen 0 E33), Z.add_0_r; reflexivity | lia | exact Vlen].
    + apply (rtm_rw_region rsegs EA (w_H W) memc 34 (pp + plen)); [exact E34u | lia | lia | | constructor].
      intros o Ho. apply Hpppres. lia.
  - unfold pa_i_slotsA, pa_i_lenA, pa_i_body. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9u, E27u, E34u. lia.
  - split; [|split].
    + cbn [pa_i_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9u, E27u, E32u, E33u, E34u. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
      rewrite Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; try lia.
      apply pa_i_mod8; assumption.
    + cbn [pa_i_factsA f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite !branch_geu_U, !U_SOff, !U_SLit, E33u.
      rewrite !pa_i_zneg by (unfold M64; lia).
      repeat split; apply negb_true_iff, Z.ltb_ge; lia.
    + cbn [pa_i_factsA f_alias alias_ok]. split; [|exact I].
      rewrite denot_lit_U, (denot_lit_U EA (SOff 34 0)). f_equal.
      rewrite U_SAlu, (U_atom EA 27 pp E27), (U_atom EA 33 plen E33), (U_atom EA 34 (pp + plen) E34) by lia.
      cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (UBx : U EA PABx = SHADOW_OFF) by (unfold PABx; apply (U_atom EA 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok rsegs PABx pa_i_SHA EA (mrestrict (w_H W) memc)).
{ constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_block rsegs B LAWS lyc Sc W memc mdc EA PABx 27 pp Layout.PP_SIZE 0 19744 HAR Hpp UBx);
    [apply (U_atom EA 27 pp E27); lia | lia | rewrite Hrq; lia].
  - apply (shent_ok_of_range rsegs (w_H W) memc EA PABx 34 (pp + plen) 32 (pp + plen) 0 32).
    + apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE); [exact HAR | exact Hpp | lia | rewrite Hrq; lia].
    + exact UBx.
    + apply (U_atom EA 34 (pp + plen) E34). lia.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
clearbody EA.
unfold cfg_at. change (w64 PA_SEL7) with (Z_to_bv 64 PA_SEL7).
(* ---- 0x80e6c .. 0x80fec, to the call at 0x51cfc ---- *)
aj_run_to_tok pa_tbl_ok HS HJ SHOK PAspan PA_I_MEMSET.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp); [reflexivity | exact E27u | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
    apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hpp0 | rewrite Hrq; lia]. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (pp + plen)); [reflexivity | exact E34u | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hpp0 | rewrite Hrq; lia]. }
(* ---- the state at the call: the bytes it wrote, the len cell, the registers ---- *)
pose proof (kept_run (fun a => pp + plen <= a < pp + plen + 16 \/ pp + 16384 <= a < pp + 16392)
  EA (ss_mem pa_i_ssA) (w_H W) memc memc (ms_mem ms) (fun _ _ _ => eq_refl) HFr) as KA.
specialize (KA ltac:(pa_i_kwr)).
assert (KRA : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pa_clob_call -> getr (ms_regs ms) r = getr regs r).
{ exact (pa_i_regs_kept EA _ ms regs pa_i_regsA (w_H W) pa_clob_call HS HR0 ltac:(vm_compute; reflexivity)). }
pa_i_reg HS (1%bv : bv 5) RA1. pa_i_reg HS (10%bv : bv 5) RA10. pa_i_reg HS (11%bv : bv 5) RA11.
pa_i_reg HS (12%bv : bv 5) RA12. pa_i_reg HS (24%bv : bv 5) RA24. pa_i_reg HS (26%bv : bv 5) RA26.
assert (KA2 : getr (ms_regs ms) 2 = getr regs 2) by pa_i_keep_reg KRA.
assert (KA3 : getr (ms_regs ms) 3 = getr regs 3) by pa_i_keep_reg KRA.
assert (KA4 : getr (ms_regs ms) 4 = getr regs 4) by pa_i_keep_reg KRA.
pa_i_regn HS 1%nat RgL.
pose proof (pa_i_field EA _ 27 pp _ _ _ _ _ 16384 8 (SOff 33 12) (plen + 12) RgL E27u ltac:(left; reflexivity)
  ltac:(apply pa_i_soff; exact E33) ltac:(cbn; lia) ltac:(cbn; lia)) as VLA.
change (N.to_nat 8) with 8%nat in VLA.
pa_i_regn HS 2%nat RgB.
assert (BODY : forall j, 0 <= j < 12 -> aview rsegs (w_H W) (ms_mem ms) (pp + plen + j) = Some (nth (Z.to_nat j) pa_int7_bytes 0)).
{ intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
  (apply (rtm_val1_aview rsegs); [| apply pa_i_bytes_range]);
  (eapply (pa_i_field EA _ 34 (pp + plen) _ _ _ _ _ _ 1); [exact RgB | exact E34u | cbn; repeat (first [left; reflexivity | right])
    | reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; apply pa_i_bytes_range | change (Z.of_N 1) with 1; lia]). }
pose proof (proj1 HJ) as HART.
rewrite (st_ok_restrict_mkst rsegs (w_H W) EA _ ms HS eq_refl) at 1.
(* ---- the call: __asan_memset(pp + plen + 12, 0, 4), ra = 0x80ff0 ---- *)
eapply SRr_bind.
{ apply (rts_intrin_at B LAWS OSet PA_I_MEMSET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (pp + plen + 12) 0 4 (R - sp0) (Z_to_bv 64 PA_I_RET) HJ).
  - rewrite RA10, (pa_i_soff EA 34 (pp + plen) 12 E34). reflexivity.
  - rewrite RA11. reflexivity.
  - rewrite RA12. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite KA2, H2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - apply pa_i_mod16_sub; assumption.
  - lia.
  - lia.
  - rewrite KA3. exact H3.
  - rewrite KA4. exact H4.
  - rewrite RA1. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split; [|lia]. replace a with (pp + (a - pp)) by lia.
    apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hpp0 | rewrite Hrq; lia].
  - eapply (amem_range_of_block rsegs B LAWS lyc Sc W (ms_mem ms) _ pp Layout.PP_SIZE); [exact HART | exact Hpp | lia | rewrite Hrq; lia].
  - eapply (range_addressable_of_block rsegs B LAWS lyc Sc W (ms_mem ms) _ pp Layout.PP_SIZE); [exact HART | exact Hpp | lia | rewrite Hrq; lia].
  - intros _. eapply (shadow_hull_vis_of_block rsegs B LAWS lyc Sc W (ms_mem ms) _ pp Layout.PP_SIZE); [exact HART | exact Hpp | lia | rewrite Hrq; lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsm2 & H10b & Heff & Hfr2).
pose proof (same_io_materialized _ _ Hsm2) as Hio2.
assert (KR2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pa_clob_call -> getr regs2 r = getr regs r).
{ intros r Hr0 Hn. rewrite (pa_i_pres _ _ r HP2 Hr0 Hn). exact (KRA r Hr0 Hn). }
assert (R24b : getr regs2 24 = w64 4).
{ transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | rewrite RA24; reflexivity]. }
assert (R26b : getr regs2 26 = w64 nr).
{ transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) |].
  rewrite RA26, (pa_i_soff EA 35 nr 0 E35), Z.add_0_r. reflexivity. }
assert (VL2 : val_mem rsegs (mrestrict (w_H W) mem2) (pp + 16384) 8 (plen + 12)).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem2 _ 8 _); [|exact VLA].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Hfr2; lia. }
assert (VI2 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 i).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) memc mem2 _ 8 _); [|exact Vi].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. rewrite Hfr2 by lia. apply KA; lia. }
assert (VE2 : val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 (2 ^ 64 - 0x4001)).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) memc mem2 _ 8 _); [|exact Ve118].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. rewrite Hfr2 by lia. apply KA; lia. }
pose proof (proj1 HJ2) as HAR2.
destruct ((al_blocks _ _ LAWS) lyc Sc W mem2 md2 pp Layout.PP_SIZE HAR2 Hpp) as (_ & _ & _ & _ & Hpppres2 & _).
rewrite Hrq in Hpppres2.
(* ---- the entry state at 0x80ff0 ---- *)
set (EB := Ereg regs2 (pa_extra [plen; pp + plen; i; nr])).
assert (F9 : ew EB 9 = Z_to_bv 64 R).
{ subst EB. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). rewrite KR2; [exact H9 | | apply pa_i_notin; vm_compute; reflexivity].
  intro Hz; vm_compute in Hz; discriminate Hz. }
assert (F27 : ew EB 27 = Z_to_bv 64 pp).
{ subst EB. rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl). rewrite KR2; [exact H27 | | apply pa_i_notin; vm_compute; reflexivity].
  intro Hz; vm_compute in Hz; discriminate Hz. }
assert (F32 : ew EB 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (F33 : ew EB 33 = Z_to_bv 64 plen) by reflexivity.
assert (F35 : ew EB 35 = Z_to_bv 64 i) by reflexivity.
assert (F36 : ew EB 36 = Z_to_bv 64 nr) by reflexivity.
assert (F9u : bv_unsigned (ew EB 9) = R) by (rewrite F9; apply unsigned_lit_small; lia).
assert (F27u : bv_unsigned (ew EB 27) = pp) by (rewrite F27; apply unsigned_lit_small; lia).
assert (F32u : bv_unsigned (ew EB 32) = SHADOW_OFF) by (rewrite F32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (F33u : bv_unsigned (ew EB 33) = plen) by (rewrite F33; apply unsigned_lit_small; lia).
assert (F35u : bv_unsigned (ew EB 35) = i) by (rewrite F35; apply unsigned_lit_small; lia).
assert (HR0B : regs_ok EB pa_i_regsB regs2).
{ unfold pa_i_regsB. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
  [subst EB; apply regs_ok_Ereg | | ] | | ] | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  - rewrite KR2 by (first [intro Hz; vm_compute in Hz; discriminate Hz | apply pa_i_notin; vm_compute; reflexivity]).
    rewrite H22. symmetry. apply (pa_i_s6_denot EB pp F27 F32); lia.
  - rewrite KR2 by (first [intro Hz; vm_compute in Hz; discriminate Hz | apply pa_i_notin; vm_compute; reflexivity]).
    rewrite H23, (pa_i_soff EB 27 pp 16384 F27). reflexivity.
  - rewrite KR2 by (first [intro Hz; vm_compute in Hz; discriminate Hz | apply pa_i_notin; vm_compute; reflexivity]).
    rewrite H18, (pa_i_soff EB 32 SHADOW_OFF 0 F32), Z.add_0_r. reflexivity.
  - rewrite R24b. reflexivity.
  - rewrite R26b, (pa_i_soff EB 36 nr 0 F36), Z.add_0_r. reflexivity. }
assert (HS2 : st_ok rsegs EB pa_i_ssB (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PA_I_RET) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs);
  change (Ereg regs2 (pa_extra [plen; pp + plen; i; nr])) with EB.
  - exact HR0B.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rtm_ro_region rsegs EB (w_H W) mem2 9 R); [exact F9u | lia | lia |].
      constructor; [|constructor; [|constructor]].
      * eapply (pa_chunk8 EB _ R 0xf8 (SOff 35 0) i); [rewrite (pa_i_soff EB 35 i 0 F35), Z.add_0_r; reflexivity | lia | exact VI2].
      * eapply (pa_chunk8 EB _ R 0x118 (SLit (-16385)) (2 ^ 64 - 0x4001)); [cbn [sv_denot]; apply Z_to_bv64_eq_mod; reflexivity | lia | exact VE2].
    + apply (rtm_rw_region rsegs EB (w_H W) mem2 27 pp); [exact F27u | lia | lia | |].
      * intros o Ho. apply Hpppres2. lia.
      * constructor; [|constructor].
        eapply (pa_chunk8 EB _ pp 0x4000 (SOff 33 12) (plen + 12)); [rewrite (pa_i_soff EB 33 plen 12 F33); reflexivity | lia | exact VL2].
  - unfold pa_i_slotsB, pa_i_lenB. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F9u, F27u. lia.
  - split; [|split; [exact I | exact I]].
    cbn [pa_i_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite F9u, F27u, F32u, F33u, F35u. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    rewrite !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; lia. }
assert (UBxB : U EB PABx = SHADOW_OFF) by (unfold PABx; apply (U_atom EB 32 SHADOW_OFF F32); unfold SHADOW_OFF; lia).
assert (SHOK2 : sh_ok rsegs PABx pa_i_SHB EB (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
  apply (shent_ok_of_block rsegs B LAWS lyc Sc W mem2 md2 EB PABx 27 pp Layout.PP_SIZE 0 19744 HAR2 Hpp UBxB);
  [apply (U_atom EB 27 pp F27); lia | lia | rewrite Hrq; lia]. }
clearbody EB.
(* ---- 0x80ff0 .. 0x81014, to 0x82530 ---- *)
aj_run_to_tok pa_tbl_ok HS2 HJ2 SHOK2 PAspan PA_LATCH7.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp); [reflexivity | exact F27u | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hpp0 | rewrite Hrq; lia]. }
pose proof (kept_run (fun a => pp + 16384 <= a < pp + 16392)
  EB (ss_mem pa_i_ssB) (w_H W) mem2 mem2 (ms_mem ms0) (fun _ _ _ => eq_refl) HFr0) as KB.
specialize (KB ltac:(pa_i_kwr)).
assert (KRB : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pa_clob_call -> getr (ms_regs ms0) r = getr regs2 r).
{ exact (pa_i_regs_kept EB _ ms0 regs2 pa_i_regsB (w_H W) pa_clob_call HS2 HR0B ltac:(vm_compute; reflexivity)). }
pa_i_reg HS2 (16%bv : bv 5) RB16. pa_i_reg HS2 (24%bv : bv 5) RB24. pa_i_reg HS2 (26%bv : bv 5) RB26.
pa_i_regn HS2 1%nat RgL3.
pose proof (pa_i_field EB _ 27 pp _ _ _ _ _ 16384 8 (SOff 33 16) (plen + 16) RgL3 F27u ltac:(left; reflexivity)
  ltac:(apply pa_i_soff; exact F33) ltac:(cbn; lia) ltac:(cbn; lia)) as VLB.
change (N.to_nat 8) with 8%nat in VLB.
(* the 16 bytes at pp + plen: 12 from the puts (kept by the call and by the last run), 4 from the memset *)
assert (AV : forall j, 0 <= j < 16 -> aview rsegs (w_H W) (ms_mem ms0) (pp + plen + j) = Some (nth (Z.to_nat j) pa_int7_bytes 0)).
{ intros j Hj. rewrite (KB (pp + plen + j)) by lia.
  destruct (Z_lt_le_dec j 12) as [Hj12 | Hj12].
  - rewrite (Hfr2 (pp + plen + j)) by lia. apply BODY. lia.
  - replace (pp + plen + j) with (pp + plen + 12 + (j - 12)) by ring. rewrite (Heff (j - 12)) by lia.
    assert (Hc : j = 12 \/ j = 13 \/ j = 14 \/ j = 15) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity. }
(* ---- the leaf ---- *)
apply SRr_ret. red.
exists lyc, Sc, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) EB _ ms0 HS2 eq_refl) at 1; reflexivity|].
split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (KRB r Hr0 Hn); exact (KR2 r Hr0 Hn)|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [eapply same_io_trans; [apply same_io_wvb | exact Hio2] | apply same_io_wvb]|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hz. cbv beta in Hz. rewrite (KB a Ha) by (intro; apply Hz; lia).
  rewrite (Hfr2 a Ha) by (intro; apply Hz; lia). apply KA; [exact Ha | intro; apply Hz; lia]. }
split; [|split; [|split; [|split]]].
- rewrite RB16, (pa_i_soff EB 35 i 0 F35), Z.add_0_r. reflexivity.
- rewrite RB24, (pa_i_soff EB 36 nr 0 F36), Z.add_0_r. reflexivity.
- rewrite RB26. reflexivity.
- intros j Hj. change (length pa_int7_bytes) with 16%nat in Hj.
  pose proof (AV (Z.of_nat j) ltac:(lia)) as A. rewrite Nat2Z.id in A. exact (rtm_aview_val1 rsegs _ _ _ _ A).
- exact VLB.
Qed.

End d.
End b.

(* ================================ the shape-7 Int pod piece: SEL7 -> LATCH7 ================================ *)
Section pi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the memset contract (__asan_memset 0x51cfc), which the Int pod block's pad calls *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51cfc.

Lemma pa_piece_int7 : rs_piece_W4_int7_stmt rsegs B MT.
Proof using MTL LAWS AMEMSET.
unfold rs_piece_W4_int7_stmt. intros cx POST rest i Hst HL7.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (pa_blk_bounds B LAWS cx Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (pa_pp_blocks B LAWS cx Hpre) as (Ppin & Ppout & PA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (_ & _ & G2 & G3 & G4 & _).
unfold rs_from_SEL7. intros ly2 S2 W2 regs2 mem2 md2 np ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hpsl & Hsh & Hnp & Hps & Hnp3).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
assert (Ppin2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
destruct (pa_img_bounds 7 ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold rs_at_cx in Hat.
pa_take Hat (LReg 9) (q_R (x_e cx)) A9. pa_take Hat (LReg 27) (q_pp (x_e cx)) A27.
pa_take Hat (LReg 23) (q_pp (x_e cx) + 0x4000) A23. pa_take Hat (LReg 22) (shadow_addr (q_pp (x_e cx) + 0x4000)) A22.
pa_take Hat (LReg 18) SHADOW_OFF A18. pa_take Hat (LReg 10) (rs_plen 7 ps) A10.
pa_take Hat (LReg 12) (rs_plen 7 ps - 0x3ffd) A12.
pa_take Hat (LReg 26) (-0x4001) A26. pa_take Hat (LReg 24) (Z.of_nat (length r)) A24.
pa_take Hat (LCell XR 0xf8) (Z.of_nat (length ps)) Af8.
pa_take Hat (LCell XR 0x118) (-0x4001) A118. pa_take Hat (LCell XR 0x130) (-0x3ffd) A130.
assert (M1 : (-0x4001) mod 2 ^ 64 = 2 ^ 64 - 0x4001) by reflexivity.
assert (M2 : (-0x3ffd) mod 2 ^ 64 = 2 ^ 64 - 0x3ffd) by reflexivity.
rewrite M1 in A118. rewrite M2 in A130. rewrite Z.mod_small in Af8 by lia.
assert (A2 : getr regs2 2 = w64 (q_R (x_e cx))) by (exact (eq_trans (Hr234 2 ltac:(lia)) RB6)).
assert (A3 : getr regs2 3 = w64 (as_gp B)) by (exact (eq_trans (Hr234 3 ltac:(lia)) G3)).
assert (A4 : getr regs2 4 = w64 (as_tp B)) by (exact (eq_trans (Hr234 4 ltac:(lia)) G4)).
assert (Hplen : rs_plen 7 ps = Z.of_nat (length (pc_buf (PbCut 7 ps None)))) by reflexivity.
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 (rs_plen 7 ps)).
{ rewrite Hplen. unfold rs_pp_at, pc_image in Hpp.
  assert (Hb16 : Z.of_nat (length (pc_buf (PbCut 7 ps None))) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
  exact (rtm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (pa_int7 B MT MTL LAWS AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (q_pp (x_e cx))
    (Z.of_nat (length ps)) (rs_plen 7 ps) (Z.of_nat (length r))
    HJ A2 A3 A4 A9 A27 A23 A22 A18 A10 A12 A26 A24 RB1 RB2 RB3 Ppin2 Ppout Af8 A118 A130 Alen _ _ _ _);
  rewrite ?Hplen; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R16 & R24 & R26 & Rpp & Rlen).
set (R := q_R (x_e cx)) in *. set (pp := q_pp (x_e cx)) in *. set (F := q_F (x_e cx)) in *.
set (plen := rs_plen 7 ps) in *.
assert (SP : spZ (x_regs cx) = R).
{ unfold spZ. rewrite RB6. unfold w64. apply unsigned_lit_small. lia. }
assert (Hcore3 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pa_core_step B MT MTL cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pa_regs234 Hkeep.
  - intros a Ha. rewrite SP. destruct Ha as [Ha|[Ha|Ha]].
    + right. apply pa_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + right. apply pa_E1_pp. fold pp. unfold Layout.PP_SIZE. lia.
    + left. unfold T_SEG_STK, ASTACK, ESTACK in *. lia. }
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_P0).
{ unfold rs_fsh_at in *. eapply rtm_fsh_kept; [exact Hfsh|]. intros j Hj.
  replace (Z.of_nat (length rs_P0)) with 56 in Hj by reflexivity. fold F.
  assert (F8 : 0 <= F / 8 <= 0xfffffff0000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in PA. unfold shadow_addr, SHADOW_OFF.
  apply Hmem; [lia|]. unfold T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *. lia. }
(* the locations the block keeps: every register of rs_Rc, s6 and s9 (none is in pa_clob_call), and every cell of
   R (the block writes only the first block's bytes and the callee's stack below R) *)
assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rs_Rc rsegs cx ++ [(LReg 22, shadow_addr (pp + 0x4000)); (LReg 25, rs_seen ps)] ++ rs_Kc rsegs cx 7 np ++
   rs_Hc rsegs cx ++ [(LCell XR 0x100, rs_cur rsegs cx rest r)])).
{ eapply pa_at_move; [pa_list; pa_from Hat|].
  cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst pa_kept_loc rt_xv].
  all: try (apply Hkeep; [cbv; discriminate | pa_notin]).
  all: let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; fold R pp; apply Hmem;
    unfold T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *; lia. }
assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None))).
{ unfold rs_pp_at. rewrite pa_img7. fold pp.
  unfold rs_pp_at, pc_image in Hpp. fold pp in Hpp.
  assert (Lx : length (prop_bytes 7 (0, PInt 0)) = 16%nat) by reflexivity.
  eapply (pa_pp_append (w_H W2) mem2 (w_H W3) mem3 pp); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite Lx, Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. lia.
  - rewrite <- Hplen. fold plen.
    replace (map (fun x : byte => bv_unsigned x) (prop_bytes 7 (0, PInt 0))) with pa_int7_bytes by (vm_compute; reflexivity).
    exact Rpp.
  - rewrite Lx, Nat2Z.inj_add, <- Hplen. fold plen. unfold Layout.OFF_LEN.
    replace (plen + Z.of_nat 16) with (plen + 16) by reflexivity. exact Rlen.
  - intros y Hy Hx Hl. rewrite Lx, <- Hplen in Hx. fold plen in Hx.
    apply Hmem; [unfold Layout.PP_SIZE in *; lia|]. unfold T_SEG_STK, ASTACK, ESTACK, Layout.OFF_LEN, Layout.PP_SIZE in *.
    cbn [Z.of_nat Pos.of_succ_nat] in Hx. lia. }
change (mkCfg (mkst regs3 (w64 PA_LATCH7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_LATCH7 regs3 mem3 md3).
apply (HL7 ly3 S3 W3 regs3 mem3 md3 7 np (ps ++ [(0, PInt 0)]) r ltac:(rewrite length_app, Hlen; cbn; lia)).
split.
- split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
  split; [apply pa_wf7; [exact Hwf | lia]|]. split; [exact Hsh|]. split; [exact Hnp|].
  split; [rewrite length_app; cbn; lia|]. split; [exact Hnp3|].
  rewrite length_app, Nat.add_1_r, pa_loop7, <- Hpsl, <- Hr. reflexivity.
- (* s10 = -0x4001, a6 = i and s8 = |r| from the block's relation; every other location kept *)
  unfold rs_at_cx. rewrite pa_seen7. pa_list; first [pa_from Hat3 | idtac].
  + cbn [rt_at]. exact R26.
  + cbn [rt_at]. refine (eq_trans R16 _). rewrite length_app. cbn. f_equal. lia.
  + cbn [rt_at]. exact R24.
Qed.
End pi.

Print Assumptions pa_piece_int7.
